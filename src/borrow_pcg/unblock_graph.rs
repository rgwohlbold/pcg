//! Data structures and algorithms related to [`UnblockGraph`].
use std::marker::PhantomData;

use crate::{
    borrow_pcg::{
        borrow_pcg_expansion::internal::BorrowPcgExpansionData,
        region_projection::{LocalLifetimeProjection, PlaceOrConst},
    },
    utils::place::maybe_remote::MaybeRemotePlace,
};

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeRef},
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{
            aggregate::AggregateEdge,
            borrow_flow::{BorrowFlowEdge, BorrowFlowEdgeKind, private::FutureEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
    },
    error::PcgInternalError,
    utils::{HasBorrowCheckerCtxt, data_structures::HashSet},
};

use super::borrow_pcg_edge::{BlockedNode, BorrowPcgEdgeLike};
use crate::{
    borrow_pcg::{edge_data::EdgeData, state::BorrowsState},
    utils::CompilerCtxt,
};

type UnblockEdge<'tcx> = BorrowPcgEdge<'tcx>;

/// A subgraph of the Borrow PCG including the edges that should be removed
/// in order to unblock a given node.
#[derive(Clone, Debug)]
pub struct UnblockGraph<'tcx, Edge = UnblockEdge<'tcx>> {
    edges: HashSet<Edge>,
    _marker: PhantomData<&'tcx ()>,
}

/// An action of unblocking nodes in the Borrow PCG.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BorrowPcgUnblockAction<'tcx, Edge = BorrowPcgEdge<'tcx>> {
    /// Removes the edge.
    RemoveEdge(Edge),
    /// Adds the edge: the aggregate edge that puts a lifetime projection back
    /// together from the nodes of its expansion once the expansion is
    /// removed, as collapsing an owned place does.
    AddEdge(Edge, PhantomData<&'tcx ()>),
}

impl<Edge> BorrowPcgUnblockAction<'_, Edge> {
    pub fn new(edge: Edge) -> Self {
        Self::RemoveEdge(edge)
    }

    /// The edge the action removes or adds.
    pub fn edge(&self) -> &Edge {
        match self {
            Self::RemoveEdge(edge) | Self::AddEdge(edge, _) => edge,
        }
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    /// Returns an ordered list of actions to unblock the edges in the graph.
    /// This is essentially a topological sort of the edges.
    pub fn actions<'a, Ctxt: HasBorrowCheckerCtxt<'a, 'tcx>>(
        self,
        ctxt: Ctxt,
    ) -> Result<Vec<BorrowPcgUnblockAction<'tcx>>, PcgInternalError>
    where
        'tcx: 'a,
        UnblockEdge<'tcx>: EdgeData<'tcx, Ctxt>,
    {
        let all_edges = self.edges.clone();
        let mut edges = self.edges;
        let mut actions = vec![];
        let mut expanded_again = HashSet::default();

        while !edges.is_empty() {
            let mut to_keep = edges.clone();

            let should_kill_edge = |edge: &UnblockEdge<'tcx>| {
                edge.blocked_by_nodes(ctxt)
                    .all(|node| edges.iter().all(|e| !e.blocks_node(node.into(), ctxt)))
            };
            for edge in &edges {
                if should_kill_edge(edge) {
                    actions.push(BorrowPcgUnblockAction::new(edge.clone()));
                    actions.extend(
                        Self::reassembly(edge)
                            .into_iter()
                            .chain(Self::reexpansion(edge, &edges, &mut expanded_again))
                            .chain(Self::lender_again(edge))
                            .chain(
                                Self::earlier_version(edge, &all_edges)
                                    .into_iter()
                                    .flatten(),
                            )
                            .map(|edge| BorrowPcgUnblockAction::AddEdge(edge, PhantomData)),
                    );
                    to_keep.remove(edge);
                }
            }
            if to_keep.len() >= edges.len() {
                return Err(PcgInternalError::new(format!(
                    "Didn't remove any leaves {edges:#?}"
                )));
            }
            edges = to_keep;
        }
        Ok(actions)
    }

    /// For the removal of an expansion of a lifetime projection into the
    /// lifetime projections of all parts of its place, the aggregate edge
    /// from those into the expanded one. An expansion into some of the parts
    /// (e.g. an element of an array) is left out: the rest of the place is
    /// in none of them.
    fn reassembly(edge: &UnblockEdge<'tcx>) -> Option<UnblockEdge<'tcx>> {
        let BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
            expansion,
        )) = edge.kind()
        else {
            return None;
        };
        if expansion.guide.is_some_and(|guide| guide.is_partial()) {
            return None;
        }
        let sources = expansion
            .expansion
            .iter()
            .map(|node| ((*node).into(), None))
            .collect();
        Some(BorrowPcgEdge::new(
            AggregateEdge::new(sources, expansion.base).into(),
            edge.conditions().clone(),
        ))
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    /// For the removal of an edge from the referent of a reborrowed place into
    /// the reborrow of the same lifetime, e.g. `(*x)|'a -> y|'a` for
    /// `y = &mut *x`, the edge from the reborrow into the referent that stands
    /// for the referent getting back what the reborrow holds, as a borrow's
    /// future edge does once the lender becomes current.
    fn lender_again(edge: &UnblockEdge<'tcx>) -> Option<UnblockEdge<'tcx>> {
        let BorrowPcgEdgeKind::BorrowFlow(flow) = edge.kind() else {
            return None;
        };
        if !matches!(
            flow.kind(),
            BorrowFlowEdgeKind::BorrowOutlives {
                regions_equal: true
            }
        ) {
            return None;
        }
        let PlaceOrConst::Place(MaybeRemotePlace::Local(lender)) = flow.long().base() else {
            return None;
        };
        Some(BorrowPcgEdge::new(
            BorrowFlowEdge::new(
                flow.short().into(),
                flow.long().with_base(lender),
                BorrowFlowEdgeKind::Future(FutureEdgeKind::FromBorrow),
            )
            .into(),
            edge.conditions().clone(),
        ))
    }

    /// For the removal of an edge from an earlier version of a lifetime
    /// projection into a later one, which holds the same contents once it has
    /// become current, the edges that give them to the earlier version again:
    /// the expansion of the later version into the parts of its expansion in
    /// `edges`, and the aggregate edge from those parts into the earlier one.
    fn earlier_version(
        edge: &UnblockEdge<'tcx>,
        edges: &HashSet<UnblockEdge<'tcx>>,
    ) -> Option<[UnblockEdge<'tcx>; 2]> {
        let BorrowPcgEdgeKind::BorrowFlow(flow) = edge.kind() else {
            return None;
        };
        if !flow.kind().is_future_to_self() || flow.short().is_future() {
            return None;
        }
        let PlaceOrConst::Place(MaybeRemotePlace::Local(earlier)) = flow.long().base() else {
            return None;
        };
        let earlier = flow.long().with_base(earlier);
        let later = flow.short();
        let parts = edges.iter().find_map(|edge| match edge.kind() {
            BorrowPcgEdgeKind::BorrowPcgExpansion(BorrowPcgExpansion::LifetimeProjection(
                expansion,
            )) if expansion.base == later
                && !expansion.guide.is_some_and(|guide| guide.is_partial()) =>
            {
                Some(expansion.expansion.clone())
            }
            _ => None,
        })?;
        let expansion = BorrowPcgExpansion::LifetimeProjection(BorrowPcgExpansionData {
            base: later,
            expansion: parts.clone(),
            guide: None,
        });
        let sources = parts.iter().map(|node| ((*node).into(), None)).collect();
        Some([
            BorrowPcgEdge::new(expansion.into(), edge.conditions().clone()),
            BorrowPcgEdge::new(
                AggregateEdge::new(sources, earlier).into(),
                edge.conditions().clone(),
            ),
        ])
    }

    /// For the removal of an edge from a part of a place's lifetime projection
    /// into the projection once it has become current, which stands for the
    /// projection being put back together from its parts, the expansion of
    /// the projection into the parts of all such edges in `edges`. It is added
    /// once per projection, recorded in `expanded_again`.
    fn reexpansion(
        edge: &UnblockEdge<'tcx>,
        edges: &HashSet<UnblockEdge<'tcx>>,
        expanded_again: &mut HashSet<LocalLifetimeProjection<'tcx>>,
    ) -> Option<UnblockEdge<'tcx>> {
        let from_part = |edge: &UnblockEdge<'tcx>| match edge.kind() {
            BorrowPcgEdgeKind::BorrowFlow(flow)
                if flow.kind().is_future_from_expansion() && !flow.short().is_future() =>
            {
                let PlaceOrConst::Place(MaybeRemotePlace::Local(part)) = flow.long().base() else {
                    return None;
                };
                Some((flow.short(), flow.long().with_base(part)))
            }
            _ => None,
        };
        let (projection, _) = from_part(edge)?;
        if !expanded_again.insert(projection) {
            return None;
        }
        let parts = edges
            .iter()
            .filter_map(from_part)
            .filter(|(target, _)| *target == projection)
            .map(|(_, part)| part)
            .collect();
        Some(BorrowPcgEdge::new(
            BorrowPcgExpansion::LifetimeProjection(BorrowPcgExpansionData {
                base: projection,
                expansion: parts,
                guide: None,
            })
            .into(),
            edge.conditions().clone(),
        ))
    }
}

impl<'tcx> UnblockGraph<'tcx> {
    pub(crate) fn new() -> Self {
        Self {
            edges: HashSet::default(),
            _marker: PhantomData,
        }
    }

    pub fn for_node(
        node: impl Into<BlockedNode<'tcx>>,
        state: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        Self::for_nodes(vec![node], state, ctxt)
    }

    pub fn for_nodes(
        nodes: impl IntoIterator<Item = impl Into<BlockedNode<'tcx>>>,
        state: &BorrowsState<'_, 'tcx>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        let mut ug = Self::new();
        for node in nodes {
            ug.unblock_node(node.into(), state, ctxt);
        }
        ug
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.edges.is_empty()
    }

    pub(crate) fn edges(&self) -> impl Iterator<Item = &UnblockEdge<'tcx>> {
        self.edges.iter()
    }

    fn add_dependency(&mut self, unblock_edge: UnblockEdge<'tcx>) -> bool {
        self.edges.insert(unblock_edge)
    }

    pub(crate) fn kill_edge<
        'a,
        Edge: BorrowPcgEdgeLike<'tcx> + EdgeData<'tcx, Ctxt>,
        Ctxt: Copy + HasBorrowCheckerCtxt<'a, 'tcx>,
    >(
        &mut self,
        edge: &Edge,
        borrows: &BorrowsState<'a, 'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
    {
        if self.add_dependency(edge.clone().to_owned_edge()) {
            for blocking_node in edge.blocked_by_nodes(ctxt) {
                self.unblock_node(blocking_node.into(), borrows, ctxt.bc_ctxt());
            }
        }
    }

    #[tracing::instrument(skip(self, borrows, ctxt))]
    pub(crate) fn unblock_node<'a: 'slf, 'slf, Ctxt: Copy + HasBorrowCheckerCtxt<'a, 'tcx>>(
        &'slf mut self,
        node: BlockedNode<'tcx>,
        borrows: &'slf BorrowsState<'a, 'tcx>,
        ctxt: Ctxt,
    ) where
        'tcx: 'a,
        BorrowPcgEdgeRef<'tcx, 'slf>: EdgeData<'tcx, Ctxt>,
    {
        for edge in borrows.edges_blocking(node, ctxt.bc_ctxt()) {
            self.kill_edge(&edge, borrows, ctxt);
        }
    }
}
