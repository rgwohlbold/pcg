use std::borrow::Cow;

use crate::{
    DebugLines,
    action::{AppliedActions, BorrowPcgAction, OwnedPcgAction, PcgActions},
    borrow_pcg::{
        borrow_pcg_edge::BorrowPcgEdge,
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{borrow::BorrowEdge, kind::BorrowPcgEdgeKind},
        edge_data::LabelNodePredicate,
        graph::{BorrowsGraph, join::JoinBorrowsArgs},
        region_projection::LifetimeProjection,
        state::{BorrowStateMutRef, BorrowStateRef, BorrowsState, BorrowsStateLike},
    },
    borrows_imgcat_debug,
    error::PcgError,
    r#loop::PlaceUsageType,
    owned_pcg::{RepackOp, join::data::JoinOwnedData},
    pcg::{
        CapabilityKind,
        ctxt::{AnalysisCtxt, HasSettings},
        obtain::{ObtainType, PlaceObtainer, expand::PlaceExpander},
        owned_state::OwnedPcg,
        place_capabilities::{PlaceCapabilities, PlaceCapabilitiesReader},
        triple::Triple,
    },
    rustc_interface::middle::mir,
    utils::{
        CompilerCtxt, DataflowCtxt, DebugImgcat, HasBorrowCheckerCtxt, Place, SnapshotLocation,
        data_structures::HashSet, display::DisplayWithCompilerCtxt, maybe_old::MaybeLabelledPlace,
        validity::HasValidityCheck,
    },
};

#[cfg(feature = "visualization")]
use crate::visualization::{dot_graph::DotGraph, generate_pcg_dot_graph};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pcg<
    'a,
    'tcx,
    Capabilities = PlaceCapabilities<'tcx>,
    EdgeKind: Eq + std::hash::Hash + PartialEq = BorrowPcgEdgeKind<'tcx>,
> {
    pub(crate) borrow: BorrowsState<'a, 'tcx, EdgeKind>,

    /// Capabilities for all places in the PCG.
    /// TODO[capability-refactor]: This map will be removed, ultimately capabilities should be
    /// computed based on the initialisation tree in the Owned PCG and the `BorrowState`
    pub(crate) place_capabilities: Capabilities,
    pub(crate) owned: OwnedPcg<'tcx>,
}

impl<'a, 'tcx: 'a, Ctxt: HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for Pcg<'a, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.as_ref().check_validity(ctxt)
    }
}

#[derive(Clone, Copy)]
pub struct PcgRef<'pcg, 'tcx> {
    pub(crate) borrow: BorrowStateRef<'pcg, 'tcx>,
    pub(crate) place_capabilities: &'pcg PlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg OwnedPcg<'tcx>,
}

impl<'tcx> PcgRef<'_, 'tcx> {
    #[cfg(feature = "visualization")]
    pub(crate) fn render_debug_graph<'slf, 'a>(
        &'slf self,
        location: mir::Location,
        debug_imgcat: Option<DebugImgcat>,
        comment: &str,
        ctxt: CompilerCtxt<'a, 'tcx>,
    ) {
        if borrows_imgcat_debug(location.block, debug_imgcat) {
            let dot_graph = generate_pcg_dot_graph(self.as_ref(), ctxt, location).unwrap();
            DotGraph::render_with_imgcat(&dot_graph, comment).unwrap_or_else(|e| {
                eprintln!("Error rendering self graph: {e}");
            });
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg Pcg<'_, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg Pcg<'_, 'tcx>) -> Self {
        Self {
            borrow: pcg.borrow.as_ref(),
            place_capabilities: &pcg.place_capabilities,
            owned: &pcg.owned,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg PcgMutRef<'pcg, 'tcx>> for PcgRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg PcgMutRef<'pcg, 'tcx>) -> Self {
        let borrow = pcg.borrow.as_ref();
        Self {
            borrow,
            place_capabilities: &*pcg.place_capabilities,
            owned: &*pcg.owned,
        }
    }
}

pub(crate) struct PcgMutRef<'pcg, 'tcx> {
    pub(crate) borrow: BorrowStateMutRef<'pcg, 'tcx>,
    pub(crate) place_capabilities: &'pcg mut PlaceCapabilities<'tcx>,
    pub(crate) owned: &'pcg mut OwnedPcg<'tcx>,
}

impl<'pcg, 'tcx> PcgMutRef<'pcg, 'tcx> {
    pub(crate) fn new(
        borrow: BorrowStateMutRef<'pcg, 'tcx>,
        place_capabilities: &'pcg mut PlaceCapabilities<'tcx>,
        owned: &'pcg mut OwnedPcg<'tcx>,
    ) -> Self {
        Self {
            borrow,
            place_capabilities,
            owned,
        }
    }
}

impl<'pcg, 'tcx> From<&'pcg mut Pcg<'_, 'tcx>> for PcgMutRef<'pcg, 'tcx> {
    fn from(pcg: &'pcg mut Pcg<'_, 'tcx>) -> Self {
        Self::new(
            (&mut pcg.borrow).into(),
            &mut pcg.place_capabilities,
            &mut pcg.owned,
        )
    }
}

pub(crate) trait PcgRefLike<'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx>;

    fn borrows_graph(&self) -> &BorrowsGraph<'tcx> {
        self.as_ref().borrow.graph
    }

    fn place_capability_equals<'b>(
        &self,
        place: Place<'tcx>,
        capability: CapabilityKind,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> bool
    where
        'tcx: 'b,
    {
        self.capability_of(place, ctxt)
            .is_some_and(|c| c == capability)
    }

    // TODO[capability-refactor]: This method will be removed, ultimately capabilities will be
    // computed based on the initialisation tree in the Owned PCG and the BorrowState.
    fn capability_of<'b>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> Option<CapabilityKind>
    where
        'tcx: 'b,
    {
        self.as_ref().place_capabilities.get(place, ctxt)
    }

    fn is_acyclic(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> bool {
        self.borrows_graph().frozen_graph().is_acyclic(ctxt)
    }

    fn owned(&self) -> &OwnedPcg<'tcx> {
        self.as_ref().owned
    }

    fn leaf_places<'a>(&self, ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>) -> HashSet<Place<'tcx>>
    where
        'tcx: 'a,
    {
        let borrows_places = self.borrows_graph().places(ctxt.bc_ctxt());
        let mut leaf_places: HashSet<Place<'tcx>> = self
            .owned()
            .leaf_places(ctxt)
            .into_iter()
            .map(Into::into)
            .filter(|p| !borrows_places.contains(p))
            .collect();
        leaf_places.extend(self.borrows_graph().leaf_places(ctxt));
        leaf_places
    }

    fn is_leaf_place<'a>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool
    where
        'tcx: 'a,
    {
        self.leaf_places(ctxt).contains(&place)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgMutRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for Pcg<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        PcgRef::from(self)
    }
}

impl<'tcx> PcgRefLike<'tcx> for PcgRef<'_, 'tcx> {
    fn as_ref(&self) -> PcgRef<'_, 'tcx> {
        *self
    }
}

impl<'a, 'tcx: 'a, Ctxt: HasSettings<'a> + HasBorrowCheckerCtxt<'a, 'tcx>> HasValidityCheck<Ctxt>
    for PcgRef<'_, 'tcx>
{
    fn check_validity(&self, ctxt: Ctxt) -> Result<(), String> {
        self.place_capabilities.check_validity(ctxt)?;
        self.borrow.check_validity(ctxt.bc_ctxt())?;
        self.owned
            .check_validity(self.place_capabilities, ctxt.bc_ctxt())?;

        if ctxt.settings().check_cycles && !self.is_acyclic(ctxt.bc_ctxt()) {
            return Err("PCG is not acyclic".to_owned());
        }

        let mut borrow_places = None;
        let mut in_borrow_graph = |place: Place<'tcx>| {
            borrow_places
                .get_or_insert_with(|| self.borrow.graph.places(ctxt.bc_ctxt()))
                .contains(&place)
        };
        for local in self.owned.unallocated_locals() {
            if in_borrow_graph(local.into()) {
                return Err(format!(
                    "Unallocated local {} is in the borrow graph",
                    local.display_string(ctxt)
                ));
            }
        }

        for (place, cap) in self.place_capabilities.iter() {
            if !self.owned.contains_place(place, ctxt.bc_ctxt())
                && !in_borrow_graph(place)
                && !place.contains_unsafe_deref(ctxt)
            {
                return Err(format!(
                    "Place {} has capability {:?} but is not in the owned PCG or borrow graph",
                    place.display_string(ctxt.bc_ctxt()),
                    cap
                ));
            }
        }

        for edge in self.borrow.graph.edges() {
            match edge.kind {
                BorrowPcgEdgeKind::Deref(deref_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = deref_edge.blocked_place
                        && let MaybeLabelledPlace::Current(deref_place) = deref_edge.deref_place
                        && let Some(c @ (CapabilityKind::Read | CapabilityKind::Exclusive)) =
                            self.place_capabilities.get(blocked_place, ctxt)
                        && self.place_capabilities.get(deref_place, ctxt).is_none()
                    {
                        return Err(format!(
                            "Deref edge {} blocked place {} has capability {:?} but deref place {} has no capability",
                            deref_edge.display_string(ctxt.bc_ctxt()),
                            blocked_place.display_string(ctxt.bc_ctxt()),
                            c,
                            deref_place.display_string(ctxt.bc_ctxt())
                        ));
                    }
                }
                BorrowPcgEdgeKind::Borrow(borrow_edge) => {
                    if let MaybeLabelledPlace::Current(blocked_place) = borrow_edge.blocked_place
                        && blocked_place.as_owned_place(ctxt).is_some()
                        && !self.owned.contains_place(blocked_place, ctxt.bc_ctxt())
                    {
                        return Err(format!(
                            "Borrow edge {} blocks owned place {}, which is not in the owned PCG",
                            borrow_edge.display_string(ctxt.bc_ctxt()),
                            blocked_place.display_string(ctxt.bc_ctxt())
                        ));
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    pub fn is_expansion_leaf(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'a, 'tcx>,
    ) -> bool {
        if self
            .borrow
            .graph()
            .edges_blocking(place.into(), ctxt.bc_ctxt())
            .any(|e| matches!(e.kind, BorrowPcgEdgeKind::BorrowPcgExpansion(_)))
        {
            return false;
        }

        match place.as_owned_place(ctxt) {
            Some(owned) => self.owned.leaf_places(ctxt).contains(&owned),
            None => true,
        }
    }

    #[must_use]
    pub fn places_with_capability(&self, capability: CapabilityKind) -> HashSet<Place<'tcx>> {
        self.place_capabilities
            .iter()
            .filter_map(|(p, c)| (c == capability).then_some(p))
            .collect()
    }

    #[must_use]
    pub fn capabilities(&self) -> &PlaceCapabilities<'tcx> {
        &self.place_capabilities
    }

    /// The tracked capability of `place`, if any (only leaves of the current
    /// pack state have entries).
    pub fn place_capability<'b>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> Option<CapabilityKind>
    where
        'tcx: 'b,
    {
        self.place_capabilities.get(place, ctxt)
    }

    /// Whether `local` is allocated and currently unpacked into sub-places.
    #[must_use]
    pub fn local_is_expanded(&self, local: mir::Local) -> bool {
        self.owned.is_allocated(local) && self.owned[local].expansions().has_expansions()
    }

    pub(crate) fn borrow_created_at(&self, location: mir::Location) -> Option<&BorrowEdge<'tcx>> {
        self.borrow.graph().borrow_created_at(location)
    }

    #[must_use]
    pub fn borrow_pcg(&self) -> &BorrowsState<'a, 'tcx> {
        &self.borrow
    }

    pub(crate) fn ensure_triple<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &mut self,
        t: Triple<'tcx>,
        ctxt: Ctxt,
    ) {
        self.owned.ensures(t, &mut self.place_capabilities, ctxt);
    }

    /// Compute the [`CapabilityKind`] of the owned place `place` from
    /// the initialisation tree alone (i.e. ignoring borrowing). See
    /// <https://prusti.github.io/pcg-docs/computing-place-capabilities.html>.
    #[must_use]
    pub fn computed_owned_capability<'b>(
        &self,
        place: Place<'tcx>,
        ctxt: impl HasBorrowCheckerCtxt<'b, 'tcx>,
    ) -> Option<CapabilityKind>
    where
        'tcx: 'b,
    {
        let owned = place.as_owned_place(ctxt)?;
        self.owned.owned_capability(owned)
    }

    // Unified capability lookup `capability_of` is provided as a
    // default method on [`PcgRefLike`] — see that trait's definition.

    /// View the maintained per-local owned-PCG state.
    #[must_use]
    pub fn owned(&self) -> &OwnedPcg<'tcx> {
        &self.owned
    }

    pub(crate) fn join_owned_data(
        &mut self,
        snapshot_location: SnapshotLocation,
    ) -> JoinOwnedData<'a, '_, 'tcx, &mut OwnedPcg<'tcx>> {
        JoinOwnedData {
            owned: &mut self.owned,
            borrows: &mut self.borrow,
            capabilities: &mut self.place_capabilities,
            snapshot_location,
        }
    }

    pub(crate) fn bridge(
        &self,
        other: &Self,
        self_block: mir::BasicBlock,
        other_block: mir::BasicBlock,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let target = other;
        let mut slf = self.clone();
        let repacks = slf.join_owned(
            target,
            SnapshotLocation::After(self_block),
            SnapshotLocation::BeforeJoin(other_block),
            ctxt,
        )?;
        let mut actions = PcgActions::new(
            repacks
                .into_iter()
                .map(|repack| OwnedPcgAction::new(repack, None).into())
                .collect(),
        );
        if ctxt.is_loop_head(other_block) {
            // A back edge removes the views that the iteration added and the
            // loop head does not have, before replaying the head's expansions.
            if ctxt.bc_ctxt().is_back_edge(self_block, other_block) {
                for edge in slf.extra_lifetime_projection_views(target.borrow.graph(), ctxt) {
                    actions.push(
                        BorrowPcgAction::remove_edge(
                            edge,
                            "bridge: a view the loop head does not have",
                        )
                        .into(),
                    );
                }
            }
            actions.extend(slf.bridge_loop_expansions(target, self_block, other_block, ctxt)?);
        } else {
            for kind in slf.missing_lifetime_projection_views(target.borrow.graph(), ctxt) {
                actions.push(
                    BorrowPcgAction::add_edge(
                        BorrowPcgEdge::new(kind, slf.borrow.validity_conditions.clone()),
                        "bridge: a view that other paths to the join have",
                    )
                    .into(),
                );
            }
        }
        Ok(actions)
    }

    /// The views in `self` (see `missing_lifetime_projection_views`) that
    /// `graph` lacks and `self` can remove: those whose parts are not
    /// blocked, i.e. not lent, apart from by views removed before them. A
    /// view through an enum's variant is a view into the variant whose part
    /// is expanded by another view, so the views are removed innermost first.
    pub(crate) fn extra_lifetime_projection_views(
        &self,
        graph: &BorrowsGraph<'tcx>,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Vec<BorrowPcgEdge<'tcx>> {
        let own = self.borrow.graph();
        let current = |node: &LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>| {
            node.label().is_none() && node.base().as_current_place().is_some()
        };
        let mut candidates = own
            .edges()
            .filter(|edge| {
                let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                    expansion,
                )) = edge.kind()
                else {
                    return false;
                };
                let base = expansion.base();
                current(&base)
                    && base
                        .base()
                        .as_current_place()
                        .is_some_and(|place| place.as_owned_place(ctxt).is_some())
                    && expansion.expansion().iter().all(current)
                    && !graph.edges().any(|other| other.kind() == edge.kind())
            })
            .collect::<Vec<_>>();
        let mut removed: Vec<BorrowPcgEdgeKind<'tcx>> = Vec::new();
        let mut result = Vec::new();
        while let Some(index) = candidates.iter().position(|edge| {
            let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                expansion,
            )) = edge.kind()
            else {
                unreachable!("the candidates are views")
            };
            expansion.expansion().iter().all(|part| {
                own.edges_blocking((*part).into(), ctxt)
                    .all(|blocking| removed.contains(blocking.kind()))
            })
        }) {
            let edge = candidates.remove(index);
            removed.push(edge.kind().clone());
            result.push(BorrowPcgEdge::new(
                edge.kind().clone(),
                edge.conditions.clone(),
            ));
        }
        result
    }

    /// The expansions in `graph` of lifetime projections of owned places
    /// that `self` lacks and can add: those of a current lifetime projection
    /// into the current ones of the place's expansion, which reading through
    /// the place creates and keeps after the place is collapsed, where the
    /// lifetime projection is not blocked in `self`. A join adds them to the
    /// predecessors that lack them, on the edges from those (see `bridge`):
    /// a view that some paths to the join have is then on every path, rather
    /// than on some paths only, where adding it again after the join would
    /// expand it twice on the paths that have it.
    pub(crate) fn missing_lifetime_projection_views(
        &self,
        graph: &BorrowsGraph<'tcx>,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Vec<BorrowPcgEdgeKind<'tcx>> {
        let own = self.borrow.graph();
        graph
            .edges()
            .filter_map(|edge| {
                let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                    expansion,
                )) = edge.kind()
                else {
                    return None;
                };
                let base = expansion.base();
                let current = |node: &LifetimeProjection<'tcx, MaybeLabelledPlace<'tcx>>| {
                    node.label().is_none() && node.base().as_current_place().is_some()
                };
                if !current(&base)
                    || base
                        .base()
                        .as_current_place()?
                        .as_owned_place(ctxt)
                        .is_none()
                    || !expansion.expansion().iter().all(current)
                    || own.edges().any(|own_edge| own_edge.kind() == edge.kind())
                    || own.edges_blocking(base.into(), ctxt).next().is_some()
                {
                    return None;
                }
                Some(edge.kind().clone())
            })
            .collect()
    }

    /// Reconcile owned layouts and capabilities. Repacking can update borrow
    /// edges, but the borrowed graphs remain separate until all predecessors
    /// have been normalized.
    pub(crate) fn join_owned(
        &mut self,
        target: &Self,
        self_snapshot: SnapshotLocation,
        other_snapshot: SnapshotLocation,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<Vec<RepackOp<'tcx>>, PcgError> {
        let mut other = target.clone();
        let mut slf_owned_data = self.join_owned_data(self_snapshot);
        let other_owned_data = JoinOwnedData {
            owned: &other.owned,
            borrows: &mut other.borrow,
            capabilities: &mut other.place_capabilities,
            snapshot_location: other_snapshot,
        };
        let mut repacks =
            slf_owned_data.join(other_owned_data, ctxt.compiler_ctxt_with_settings())?;
        for (place, cap) in self.place_capabilities.iter() {
            let Some(_owned) = place.as_owned_place(ctxt) else {
                continue;
            };
            if let Some(other_cap) = other.place_capabilities.get(place, ctxt)
                && cap > other_cap
            {
                repacks.push(RepackOp::weaken(place, cap, other_cap));
            }
        }
        self.place_capabilities
            .join(&other.place_capabilities, ctxt);
        self.owned.join_capabilities(&other.owned);
        Ok(repacks)
    }

    fn bridge_loop_expansions(
        &mut self,
        other: &Self,
        self_block: mir::BasicBlock,
        loop_head: mir::BasicBlock,
        ctxt: impl DataflowCtxt<'a, 'tcx>,
    ) -> Result<PcgActions<'tcx>, PcgError> {
        let mut expansions = Vec::new();
        // The lifetime projections of owned places expanded at the loop head:
        // `join_owned` expands the places themselves, but not their lifetime
        // projections.
        let mut owned_lifetime_expansions = Vec::new();
        for edge in other.borrow.graph().edges() {
            let conditions = edge.conditions.without_branch_choice(self_block);
            // The guide is kept: the target place does not carry the label of
            // an index guide.
            let (base, target, guide) = match edge.kind() {
                BorrowPcgEdgeKind::Deref(deref) => {
                    (deref.blocked_place(), deref.deref_place(), None)
                }
                BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::Place(expansion)) => {
                    let Some(target) = expansion.expansion().first() else {
                        continue;
                    };
                    (expansion.base(), *target, expansion.guide)
                }
                BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                    expansion,
                )) => {
                    if let (Some(base), Some(target)) = (
                        expansion.base().base().as_current_place(),
                        expansion
                            .expansion()
                            .first()
                            .and_then(|target| target.base().as_current_place()),
                    ) && base.as_owned_place(ctxt).is_some()
                    {
                        owned_lifetime_expansions.push((base, target, conditions));
                    }
                    continue;
                }
                _ => continue,
            };
            if let (Some(base), Some(target)) = (base.as_current_place(), target.as_current_place())
            {
                expansions.push((base, target, guide, conditions));
            }
        }
        // A place expansion or deref replayed below expands the lifetime
        // projections of its base itself, and one expansion of a base
        // expands all its lifetime projections.
        owned_lifetime_expansions.retain(|(base, _, _)| {
            !expansions
                .iter()
                .any(|(other_base, _, _, _)| other_base == base)
        });
        owned_lifetime_expansions.sort_by_key(|(base, target, _)| (*base, *target));
        owned_lifetime_expansions.dedup_by_key(|(base, _, _)| *base);
        let mut expansions = expansions
            .into_iter()
            .map(|(base, target, guide, conditions)| (base, target, guide, conditions, false))
            .chain(
                owned_lifetime_expansions
                    .into_iter()
                    .map(|(base, target, conditions)| (base, target, None, conditions, true)),
            )
            .collect::<Vec<_>>();
        expansions.sort_by_key(|(base, _, _, _, _)| base.projection.len());
        let mut applied = AppliedActions::default();
        for (base, target, guide, conditions, lifetimes_only) in expansions {
            // On a back edge, the expansion is still there from the loop head.
            if lifetimes_only && self.contains_lifetime_projection_expansion(base, target) {
                continue;
            }
            let usage_type =
                if other.place_capabilities.get(base, ctxt) == Some(CapabilityKind::Read) {
                    PlaceUsageType::Read
                } else {
                    PlaceUsageType::Exclusive
                };
            let obtain_type = ObtainType::LoopInvariant {
                is_blocked: false,
                usage_type,
            };
            let expansion = base.expand_one_level(target, ctxt)?;
            let mut pcg = PcgMutRef::from(&mut *self);
            // The current CFG edge's branch choice has already been removed.
            // Keep guards from earlier branches.
            pcg.borrow.validity_conditions = &conditions;
            let mut obtainer = PlaceObtainer::new(
                pcg,
                Some(&mut applied),
                ctxt,
                mir::Location {
                    block: loop_head,
                    statement_index: 0,
                },
                SnapshotLocation::Loop(loop_head),
            );
            if !obtainer.contains_expansion(base, &expansion, guide, ctxt)? {
                // The expansion may snapshot the current projections of `base`
                // with the loop-head label, while the graph still holds the
                // loop-head snapshots taken when this iteration began. If both
                // are present they would become one node, so the old snapshot
                // is first relabelled as the snapshot after the predecessor
                // block.
                for rp in base.lifetime_projections(ctxt) {
                    let current = rp.with_base(MaybeLabelledPlace::Current(rp.base));
                    let snapshot =
                        current.with_label(Some(SnapshotLocation::Loop(loop_head).into()), ctxt);
                    let graph = obtainer.borrows_graph();
                    if graph.contains(current, ctxt) && graph.contains(snapshot, ctxt) {
                        obtainer.record_and_apply_action(
                            BorrowPcgAction::label_lifetime_projection(
                                LabelNodePredicate::equals_lifetime_projection(snapshot),
                                Some(SnapshotLocation::After(self_block).into()),
                                "bridge: relabel the iteration's loop-head snapshot",
                            )
                            .into(),
                        )?;
                    }
                }
            }
            if lifetimes_only
                || obtainer.expand_place_one_level(base, &expansion, guide, obtain_type, ctxt)?
            {
                // The bridge replays the loop head's expansions, which stand
                // for the whole loop body, so every projection may change.
                obtainer.expand_lifetime_projections_one_level(
                    base,
                    &expansion,
                    None,
                    obtain_type,
                    ctxt,
                )?;
            }
        }
        Ok(PcgActions::new(
            applied.actions.into_iter().map(|a| a.action).collect(),
        ))
    }

    /// Whether a lifetime projection of `base` is expanded to one of `target`.
    fn contains_lifetime_projection_expansion(
        &self,
        base: Place<'tcx>,
        target: Place<'tcx>,
    ) -> bool {
        self.borrow.graph().edges().any(|edge| {
            let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                expansion,
            )) = edge.kind()
            else {
                return false;
            };
            expansion.base().base().as_current_place() == Some(base)
                && expansion
                    .expansion()
                    .iter()
                    .any(|node| node.base().as_current_place() == Some(target))
        })
    }

    #[tracing::instrument(skip(self, other, ctxt))]
    pub(crate) fn merge_borrows(
        &mut self,
        other: &Self,
        other_block: mir::BasicBlock,
        ctxt: AnalysisCtxt<'a, 'tcx>,
    ) {
        let mut other_borrows = other.borrow.clone();
        other_borrows.add_cfg_edge(other_block, ctxt.block, ctxt);
        self.place_capabilities
            .join(&other.place_capabilities, ctxt);
        self.owned.join_capabilities(&other.owned);
        self.borrow.merge(&other_borrows, ctxt);
    }

    pub(crate) fn finish_join(&mut self, ctxt: AnalysisCtxt<'a, 'tcx>) {
        let borrow_args = JoinBorrowsArgs {
            self_block: ctxt.block,
            body_analysis: ctxt.body_analysis,
            capabilities: &mut self.place_capabilities,
            owned: &mut self.owned,
        };
        self.borrow.finish_join(borrow_args, ctxt);
    }

    pub(crate) fn debug_lines<Ctxt: HasBorrowCheckerCtxt<'a, 'tcx> + HasSettings<'a>>(
        &self,
        ctxt: Ctxt,
    ) -> Vec<Cow<'static, str>> {
        let mut result = self.borrow.debug_lines(ctxt);
        result.sort();
        let mut capabilities = self.place_capabilities.debug_lines(ctxt);
        capabilities.sort();
        result.extend(capabilities);
        result
    }
}

impl<'a, 'tcx: 'a> Pcg<'a, 'tcx> {
    pub(crate) fn start_block(analysis_ctxt: AnalysisCtxt<'a, 'tcx>) -> Self {
        let mut capabilities: PlaceCapabilities<'tcx> = PlaceCapabilities::default();
        let owned = OwnedPcg::start_block(&mut capabilities, analysis_ctxt);
        let borrow = BorrowsState::start_block(&mut capabilities, analysis_ctxt);
        Pcg {
            borrow,
            place_capabilities: capabilities,
            owned,
        }
    }
}
