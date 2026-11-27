//! A client of the PCG's results that replays the PCG's actions as transfers
//! of contents between the lifetime projections of the borrow graph, and
//! compares the nodes that hold contents with those that the graph's shape
//! says hold them.
//!
//! The replay keeps a set of *full* nodes and changes it only on the PCG's
//! actions. Each phase starts from the PCG's graph before the phase, which
//! then changes only by the phase's actions. At the end of every phase of a
//! statement, and on every
//! edge of the control-flow graph, it compares the full nodes that appear in
//! an edge with the *leaves* of the graph:
//!
//! - a lifetime projection that appears in an edge of the borrow graph,
//! - that is not a future node and not a node of the caller,
//! - whose base is not a place without a value (with only write capability),
//! - that is not a current projection that is only the source of future
//!   edges, with no edge into it (it stands for the value its place gets
//!   next),
//! - and that is not blocked by an edge into a non-future node.
//!
//! A leaf that is not full is *missing* (nothing gave it contents) and a full
//! node that is not a leaf is *extra* (it holds contents, but is blocked).
//! Each phase with a missing or an extra node is a *mismatch*.
//!
//! The rules of the replay (the "who gives contents to whom" of each action):
//!
//! 1. **Renames** (labelling a place or lifetime projection, unlabelling, a
//!    restore): fullness follows the node to its new name.
//! 2. **A future node becomes current** (a rename from a future node to a
//!    current one): it takes the contents of the full sources of the
//!    `FromBorrow` and `FromExpansion` future edges into it. If there are such
//!    sources and none is full, the node takes nothing: a *rule P failure*.
//!    A source that is the future node of an earlier version of a place,
//!    which no restore makes current, passes on what flows into it: its own
//!    sources are taken from instead (transit). A source that gave to a future
//!    node earlier in the phase can give to another one as well. Without such
//!    sources, it takes the contents of its earlier version (the
//!    source of a `ToFutureSelf` edge).
//! 3. **An added edge** (other than a future edge) into a place empties its
//!    full lifetime-projection sources (their contents leave the borrow graph). An added edge into
//!    lifetime projections fills them if a source is full, was emptied by an
//!    added edge earlier in the phase, is a place or a node of the caller, or
//!    the edge is the assignment of a constant; it empties its full
//!    lifetime-projection sources.
//! 4. **A removed edge** that is not a future edge, does not lead into a
//!    future node and does not assign a constant gives back: an edge into a
//!    place fills its lifetime-projection sources; another edge fills them if
//!    one of its targets is full or gave back earlier in the phase, and empties
//!    its targets. An `outlives` edge whose source is still blocked by another
//!    edge gives nothing back: the other edge (e.g. a mutable borrow) returns
//!    the contents.
//! 5. **A node that enters the graph** holds the contents it held as part of
//!    its place: a lifetime projection that an added edge (not a future edge)
//!    brings in as a source is full before the edge's transfer. Another node
//!    that enters the graph with no edge into it, unlabelled, not a future
//!    node and in an edge other than a future edge, is created full (e.g. the
//!    result of a call that borrows from nothing in the graph).
//! 6. A full lifetime projection with a dereference edge into a place is
//!    emptied.
//! 7. At the end of a phase, the current lifetime projections of a place
//!    without a value are emptied: what they held left with the value (e.g.
//!    the result's contents, which go to the caller at the return). This rule
//!    reads the PCG's capabilities; each use is reported.
//! 8. An output of a function call's edge that gave its contents back to its
//!    lender through a future edge (rule 2) holds nothing, although it stays a
//!    leaf of the call's edge, which the call's other outputs still need. It
//!    is not counted as a leaf; each use is reported.
//!
//! The replay is enabled in `pcg_bin` with `PCG_HOLDERS_REPLAY=<file>`; it
//! appends one JSON line per function to the file.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use serde_json::{Value, json};

use crate::{
    PcgOutput,
    action::PcgAction,
    borrow_pcg::{
        action::BorrowPcgActionKind,
        borrow_pcg_edge::BorrowPcgEdge,
        edge::{
            abstraction::FunctionCallOrLoop,
            borrow_flow::{BorrowFlowEdgeKind, OperandType, private::FutureEdgeKind},
            kind::BorrowPcgEdgeKind,
        },
        edge_data::{EdgeData, NodeReplacement},
        graph::BorrowsGraph,
        region_projection::{LifetimeProjectionLabel, PlaceOrConst},
        validity_conditions::{ValidityConditions, ValidityConditionsLike},
        visitor::{GeneralizedLifetime, OpaqueTy},
    },
    pcg::{
        CapabilityKind, EvalStmtPhase, MaybeHasLocation, Pcg, PcgNode,
        place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::{self, BasicBlock},
            ty,
        },
    },
    utils::{
        CompilerCtxt, Place, SnapshotLocation,
        display::DisplayWithCtxt,
        place::{maybe_old::MaybeLabelledPlace, maybe_remote::MaybeRemotePlace},
    },
};

type Node<'tcx> = PcgNode<'tcx>;

/// The places that hold only write capability in `pcg`.
fn without_value<'tcx>(pcg: &Pcg<'_, 'tcx>) -> HashSet<Place<'tcx>> {
    pcg.capabilities()
        .iter()
        .filter(|(_, capability)| *capability == CapabilityKind::Write)
        .map(|(place, _)| place)
        .collect()
}

/// The kind of an edge, as far as the replay distinguishes them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum EdgeClass {
    Borrow { mutable: bool },
    Expansion,
    Deref,
    FunctionCall,
    Loop,
    Outlives { equal: bool },
    InitialBorrows,
    Move,
    Copy,
    Const,
    Future(FutureClass),
    Aggregate,
    Coupled,
    Delegation,
    RawPtrDeref,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum FutureClass {
    FromExpansion,
    FromBorrow,
    ToFutureSelf,
}

impl EdgeClass {
    fn name(self) -> &'static str {
        match self {
            EdgeClass::Borrow { mutable: true } => "borrow_mut",
            EdgeClass::Borrow { mutable: false } => "borrow_shared",
            EdgeClass::Expansion => "expansion",
            EdgeClass::Deref => "deref",
            EdgeClass::FunctionCall => "call",
            EdgeClass::Loop => "loop",
            EdgeClass::Outlives { equal: true } => "equals",
            EdgeClass::Outlives { equal: false } => "outlives",
            EdgeClass::InitialBorrows => "initial",
            EdgeClass::Move => "move",
            EdgeClass::Copy => "copy",
            EdgeClass::Const => "const",
            EdgeClass::Future(FutureClass::FromExpansion) => "future_from_expansion",
            EdgeClass::Future(FutureClass::FromBorrow) => "future_from_borrow",
            EdgeClass::Future(FutureClass::ToFutureSelf) => "future_to_self",
            EdgeClass::Aggregate => "aggregate",
            EdgeClass::Coupled => "coupled",
            EdgeClass::Delegation => "delegation",
            EdgeClass::RawPtrDeref => "rawptr_deref",
        }
    }

    fn is_future(self) -> bool {
        matches!(self, EdgeClass::Future(_))
    }
}

/// An edge of the borrow graph as the replay sees it: its kind, the nodes it
/// blocks (its sources) and the nodes that block them (its targets).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Edge<'tcx> {
    class: EdgeClass,
    sources: Vec<Node<'tcx>>,
    targets: Vec<Node<'tcx>>,
}

impl<'tcx> Edge<'tcx> {
    fn new(kind: &BorrowPcgEdgeKind<'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> Self {
        let class = match kind {
            BorrowPcgEdgeKind::Borrow(borrow) => EdgeClass::Borrow {
                mutable: borrow.is_mut(),
            },
            BorrowPcgEdgeKind::BorrowPcgExpansion(_) => EdgeClass::Expansion,
            BorrowPcgEdgeKind::Deref(_) => EdgeClass::Deref,
            BorrowPcgEdgeKind::Abstraction(FunctionCallOrLoop::FunctionCall(_)) => {
                EdgeClass::FunctionCall
            }
            BorrowPcgEdgeKind::Abstraction(FunctionCallOrLoop::Loop(_)) => EdgeClass::Loop,
            BorrowPcgEdgeKind::BorrowFlow(flow) => match flow.kind {
                BorrowFlowEdgeKind::BorrowOutlives { regions_equal } => EdgeClass::Outlives {
                    equal: regions_equal,
                },
                BorrowFlowEdgeKind::InitialBorrows => EdgeClass::InitialBorrows,
                BorrowFlowEdgeKind::Assignment(data) => match data.operand_type() {
                    OperandType::Move => EdgeClass::Move,
                    OperandType::Copy => EdgeClass::Copy,
                    OperandType::Const => EdgeClass::Const,
                },
                BorrowFlowEdgeKind::Future(kind) => EdgeClass::Future(match kind {
                    FutureEdgeKind::FromExpansion => FutureClass::FromExpansion,
                    FutureEdgeKind::FromBorrow => FutureClass::FromBorrow,
                    FutureEdgeKind::ToFutureSelf => FutureClass::ToFutureSelf,
                }),
            },
            BorrowPcgEdgeKind::Aggregate(_) => EdgeClass::Aggregate,
            BorrowPcgEdgeKind::Coupled(_) => EdgeClass::Coupled,
            BorrowPcgEdgeKind::Delegation(_) => EdgeClass::Delegation,
            BorrowPcgEdgeKind::RawPtrDeref(_) => EdgeClass::RawPtrDeref,
        };
        Edge {
            class,
            sources: kind.blocked_nodes(ctxt).collect(),
            targets: kind.blocked_by_nodes(ctxt).map(Into::into).collect(),
        }
    }

    fn renamed(&self, renames: &HashMap<Node<'tcx>, Node<'tcx>>) -> Self {
        let rename = |n: &Node<'tcx>| *renames.get(n).unwrap_or(n);
        Edge {
            class: self.class,
            sources: self.sources.iter().map(rename).collect(),
            targets: self.targets.iter().map(rename).collect(),
        }
    }

    fn nodes(&self) -> impl Iterator<Item = Node<'tcx>> + '_ {
        self.sources.iter().chain(self.targets.iter()).copied()
    }

    /// Whether the edge blocks its sources: it does unless all its targets
    /// are future nodes.
    fn blocks(&self) -> bool {
        self.targets.iter().any(|t| !is_future(*t))
    }

    /// Whether the edge is an `outlives` edge whose targets that are not
    /// future nodes are all lifetime projections of the body that the replay
    /// does not track: they cannot hold a mutable loan, so the edge (e.g. of
    /// a shared reborrow) takes no contents from its sources.
    fn only_into_untracked(&self, tracked: &impl Fn(Node<'tcx>) -> bool) -> bool {
        matches!(self.class, EdgeClass::Outlives { .. })
            && self
                .targets
                .iter()
                .filter(|t| !is_future(**t))
                .all(|t| !is_outside(*t) && !tracked(*t))
    }

    fn display(&self, ctxt: CompilerCtxt<'_, 'tcx>) -> String {
        let show = |ns: &[Node<'tcx>]| {
            ns.iter()
                .map(|n| n.display_string(ctxt))
                .collect::<Vec<_>>()
                .join(", ")
        };
        format!(
            "{{{}}} -{}-> {{{}}}",
            show(&self.sources),
            self.class.name(),
            show(&self.targets)
        )
    }
}

fn is_lp(n: Node<'_>) -> bool {
    matches!(n, PcgNode::LifetimeProjection(_))
}

fn is_future(n: Node<'_>) -> bool {
    matches!(n, PcgNode::LifetimeProjection(lp) if lp.label() == Some(LifetimeProjectionLabel::Future))
}

/// Whether `lifetime` occurs in `ty` as the lifetime of a mutable reference
/// reached through mutable references only, or may (see
/// [`Replay::carries_mutable_loan`]).
fn mutable_occurrence<'tcx>(
    ty: ty::Ty<'tcx>,
    lifetime: GeneralizedLifetime<'tcx>,
    tcx: ty::TyCtxt<'tcx>,
    visited: &mut HashSet<DefId>,
) -> bool {
    let rec =
        |ty: ty::Ty<'tcx>, visited: &mut HashSet<_>| mutable_occurrence(ty, lifetime, tcx, visited);
    match ty.kind() {
        ty::TyKind::Ref(region, inner, mutability) => {
            mutability.is_mut()
                && (lifetime == GeneralizedLifetime::Region((*region).into())
                    || rec(*inner, visited))
        }
        ty::TyKind::RawPtr(inner, mutability) => mutability.is_mut() && rec(*inner, visited),
        ty::TyKind::Adt(def, args) => {
            if def.is_box() {
                return rec(args.type_at(0), visited);
            }
            if !visited.insert(def.did()) {
                return false;
            }
            def.all_fields()
                .any(|field| rec(crate::rustc_interface::field_ty(field, tcx, args), visited))
        }
        ty::TyKind::Tuple(tys) => tys.iter().any(|ty| rec(ty, visited)),
        ty::TyKind::Array(elem, _) | ty::TyKind::Slice(elem) => rec(*elem, visited),
        ty::TyKind::Closure(_, args) => rec(args.as_closure().tupled_upvars_ty(), visited),
        ty::TyKind::Param(_) => OpaqueTy::try_from(ty)
            .is_ok_and(|opaque| lifetime == GeneralizedLifetime::RegionsIn(opaque)),
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_)
        | ty::TyKind::Str
        | ty::TyKind::Never
        | ty::TyKind::FnDef(..)
        | ty::TyKind::FnPtr(..) => false,
        // Aliases, trait objects and the rest: conservatively.
        _ => true,
    }
}

/// `n` without the labels of `loop_head`'s join and of the loop head itself.
fn strip_loop_labels<'tcx>(
    n: Node<'tcx>,
    loop_head: BasicBlock,
    ctxt: CompilerCtxt<'_, 'tcx>,
) -> Node<'tcx> {
    let at_head = |location: Option<SnapshotLocation>| {
        matches!(
            location,
            Some(SnapshotLocation::BeforeJoin(b) | SnapshotLocation::Loop(b)) if b == loop_head
        )
    };
    let unlabel = |p: MaybeLabelledPlace<'tcx>| {
        if at_head(p.location()) {
            MaybeLabelledPlace::Current(p.place())
        } else {
            p
        }
    };
    match n {
        PcgNode::Place(p) => PcgNode::Place(unlabel(p)),
        PcgNode::LifetimeProjection(mut lp) => {
            if let PlaceOrConst::Place(MaybeRemotePlace::Local(p)) = lp.base {
                lp.base = PlaceOrConst::Place(MaybeRemotePlace::Local(unlabel(p)));
            }
            if let Some(LifetimeProjectionLabel::Location(location)) = lp.label()
                && at_head(Some(location))
            {
                lp = lp.with_label(None, ctxt);
            }
            PcgNode::LifetimeProjection(lp)
        }
    }
}

/// Whether the node is a lifetime projection of a labelled place.
fn has_labelled_base(n: Node<'_>) -> bool {
    matches!(
        n,
        PcgNode::LifetimeProjection(lp)
            if matches!(lp.base, PlaceOrConst::Place(MaybeRemotePlace::Local(p)) if p.is_old())
    )
}

fn is_remote(n: Node<'_>) -> bool {
    matches!(
        n,
        PcgNode::LifetimeProjection(lp)
            if matches!(lp.base, PlaceOrConst::Place(MaybeRemotePlace::Remote(_)))
    )
}

fn is_const(n: Node<'_>) -> bool {
    matches!(n, PcgNode::LifetimeProjection(lp) if matches!(lp.base, PlaceOrConst::Const(_)))
}

/// Whether the node holds contents outside the borrow graph: a place, a node
/// of the caller, or a lifetime projection of a constant.
fn is_outside(n: Node<'_>) -> bool {
    !is_lp(n) || is_remote(n) || is_const(n)
}

/// Whether the lifetime projection carries a label (other than the future
/// label), or its base is a labelled place.
fn is_labelled(n: Node<'_>) -> bool {
    match n {
        PcgNode::LifetimeProjection(lp) => {
            matches!(lp.label(), Some(LifetimeProjectionLabel::Location(_)))
                || matches!(
                    lp.base,
                    PlaceOrConst::Place(MaybeRemotePlace::Local(p)) if p.is_old()
                )
        }
        PcgNode::Place(p) => p.is_old(),
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Graph<'tcx> {
    edges: HashSet<Edge<'tcx>>,
    /// The places that hold no value (only write capability) in the state of
    /// the graph: their lifetime projections hold nothing.
    without_value: HashSet<Place<'tcx>>,
}

impl<'tcx> Graph<'tcx> {
    fn of(
        graph: &BorrowsGraph<'tcx>,
        without_value: HashSet<Place<'tcx>>,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        Graph {
            edges: graph.edges().map(|e| Edge::new(e.kind(), ctxt)).collect(),
            without_value,
        }
    }

    /// The graph on entry to `to` coming from `from`, whose path conditions
    /// are `path`: without the edges that are valid only on other paths into
    /// `to` (e.g. those of the other branch at a join).
    fn on_cfg_edge(
        graph: &BorrowsGraph<'tcx>,
        without_value: HashSet<Place<'tcx>>,
        path: &ValidityConditions,
        from: BasicBlock,
        to: BasicBlock,
        ctxt: CompilerCtxt<'_, 'tcx>,
    ) -> Self {
        let body = ctxt.body();
        let valid = |conditions: &ValidityConditions| {
            conditions.all_branch_choices().all(|choice| {
                let chosen = choice.successors(body);
                if choice.from() == from {
                    return chosen.contains(&to);
                }
                path.all_branch_choices()
                    .find(|taken| taken.from() == choice.from())
                    .is_none_or(|taken| taken.successors(body).iter().any(|s| chosen.contains(s)))
            })
        };
        Graph {
            edges: graph
                .edges()
                .filter(|e| valid(e.conditions))
                .map(|e| Edge::new(e.kind(), ctxt))
                .collect(),
            without_value,
        }
    }

    fn of_state(pcg: &Pcg<'_, 'tcx>, ctxt: CompilerCtxt<'_, 'tcx>) -> Self {
        Self::of(pcg.borrow_pcg().graph(), without_value(pcg), ctxt)
    }

    /// Whether the node is a lifetime projection of a place without a value.
    fn has_no_value(&self, n: Node<'tcx>) -> bool {
        matches!(
            n,
            PcgNode::LifetimeProjection(lp)
                if matches!(
                    lp.base,
                    PlaceOrConst::Place(MaybeRemotePlace::Local(MaybeLabelledPlace::Current(p)))
                        if self.without_value.contains(&p)
                )
        )
    }

    fn nodes(&self) -> HashSet<Node<'tcx>> {
        self.edges.iter().flat_map(Edge::nodes).collect()
    }

    fn blocked(&self) -> HashSet<Node<'tcx>> {
        self.edges
            .iter()
            .filter(|e| e.blocks())
            .flat_map(|e| e.sources.iter().copied())
            .collect()
    }

    /// Whether the node is an output of a function call's edge.
    fn is_call_output(&self, n: Node<'tcx>) -> bool {
        self.edges.iter().any(|e| {
            matches!(e.class, EdgeClass::Coupled | EdgeClass::FunctionCall)
                && e.targets.contains(&n)
        })
    }

    fn has_incoming(&self, n: Node<'tcx>) -> bool {
        self.edges.iter().any(|e| e.targets.contains(&n))
    }

    /// Whether the node appears in an edge that is not a future edge.
    fn in_non_future_edge(&self, n: Node<'tcx>) -> bool {
        self.edges
            .iter()
            .any(|e| !e.class.is_future() && e.nodes().any(|m| m == n))
    }

    /// Whether the node is a current lifetime projection that is only the
    /// source of future edges, with no edge into it: it stands for the value its place gets next, e.g. the projection
    /// of a dropped place that a write gives a new value, which the future
    /// node of the place's parent takes when it becomes current.
    fn is_placeholder(&self, n: Node<'tcx>) -> bool {
        matches!(n, PcgNode::LifetimeProjection(lp) if lp.label().is_none())
            && !has_labelled_base(n)
            && self.edges.iter().all(|e| {
                !e.targets.contains(&n) && (e.class.is_future() || !e.sources.contains(&n))
            })
    }

    /// The nodes that hold their contents according to the graph's shape.
    /// An edge into lifetime projections that are all untracked (e.g. of a
    /// shared reborrow) freezes its sources, which keep their contents.
    fn leaves(&self, tracked: &impl Fn(Node<'tcx>) -> bool) -> HashSet<Node<'tcx>> {
        let blocked = self
            .edges
            .iter()
            .filter(|e| e.blocks() && !e.only_into_untracked(tracked))
            .flat_map(|e| e.sources.iter().copied())
            .collect::<HashSet<_>>();
        self.nodes()
            .into_iter()
            .filter(|n| {
                tracked(*n)
                    && !is_future(*n)
                    && !blocked.contains(n)
                    && !self.has_no_value(*n)
                    && !self.is_placeholder(*n)
            })
            .collect()
    }

    fn renamed(&self, renames: &HashMap<Node<'tcx>, Node<'tcx>>) -> Self {
        let mut graph = self.clone();
        graph.rename(renames);
        graph
    }

    fn rename(&mut self, renames: &HashMap<Node<'tcx>, Node<'tcx>>) {
        self.edges = self.edges.iter().map(|e| e.renamed(renames)).collect();
    }
}

/// The state of the replay.
#[derive(Clone, Default)]
struct State<'tcx> {
    graph: Graph<'tcx>,
    full: HashSet<Node<'tcx>>,
    /// Nodes emptied by an added edge in the current phase.
    spent: HashSet<Node<'tcx>>,
    /// Nodes that gave to a future node that became current in the current
    /// phase: they can give to another one as well (rule 2).
    gave_to_future_now: HashSet<Node<'tcx>>,
    /// Nodes that gave their contents back in the current phase.
    gave: HashSet<Node<'tcx>>,
    /// Nodes that gave their contents to a future node that became current
    /// (rule 2) and have been empty since (for rule 8 and the report).
    gave_to_future: HashSet<Node<'tcx>>,
    /// The call outputs already reported for rule 8.
    reported_outputs: HashSet<Node<'tcx>>,
    /// Full nodes that the graph's shape says are blocked, reported once:
    /// a client following the actions still holds their contents.
    lost: HashSet<Node<'tcx>>,
}

/// Counters and findings of the replay of one function.
#[derive(Default)]
struct Report {
    phases: usize,
    changed: usize,
    matched: usize,
    edges_checked: usize,
    edges_matched: usize,
    rule_p_failures: Vec<Value>,
    mismatches: Vec<Value>,
    /// Removals of edges that the replay's graph does not have.
    unknown_removals: Vec<Value>,
    /// Full nodes emptied at the end of a phase because their place has no
    /// value (rule 7).
    dropped_with_value: Vec<Value>,
    /// Call outputs that are leaves but gave their contents back (rule 8).
    emptied_call_outputs: Vec<Value>,
}

struct Replay<'a, 'tcx> {
    ctxt: CompilerCtxt<'a, 'tcx>,
    /// Whether a lifetime projection carries a mutable loan, by node.
    mutable_loan: std::cell::RefCell<HashMap<Node<'tcx>, bool>>,
    report: Report,
    /// The location being replayed, for the report.
    at: String,
    stmt: String,
    stmt_kind: String,
}

impl<'a, 'tcx> Replay<'a, 'tcx> {
    /// Whether the node holds contents outside the tracked part of the
    /// borrow graph: a place, a node of the caller, a lifetime projection of
    /// a constant, or a lifetime projection that carries no mutable loan
    /// (e.g. of a shared reference: its predicate is `true`).
    fn is_owned(&self, n: Node<'tcx>) -> bool {
        is_outside(n) || !self.carries_mutable_loan(n)
    }

    /// A lifetime projection whose contents the replay tracks.
    fn is_tracked(&self, n: Node<'tcx>) -> bool {
        is_lp(n) && !self.is_owned(n)
    }

    /// Whether the lifetime projection's lifetime is that of a mutable
    /// reference in its place's type, reached through mutable references
    /// only (a mutable reference behind a shared one is frozen). A type
    /// parameter's `RegionsIn(T)`, an alias and a trait object may hold
    /// mutable references and count as carrying one.
    fn carries_mutable_loan(&self, n: Node<'tcx>) -> bool {
        let PcgNode::LifetimeProjection(lp) = n else {
            return false;
        };
        let PlaceOrConst::Place(MaybeRemotePlace::Local(base)) = lp.base else {
            return false;
        };
        if let Some(known) = self.mutable_loan.borrow().get(&n) {
            return *known;
        }
        let lifetime: GeneralizedLifetime<'tcx> = lp.region(self.ctxt);
        let ty = base.place().ty(self.ctxt).ty;
        let result = mutable_occurrence(ty, lifetime, self.ctxt.tcx(), &mut HashSet::default());
        self.mutable_loan.borrow_mut().insert(n, result);
        result
    }

    fn show(&self, n: Node<'tcx>) -> String {
        n.display_string(self.ctxt)
    }

    fn show_set(&self, ns: impl IntoIterator<Item = Node<'tcx>>) -> Vec<String> {
        ns.into_iter().map(|n| self.show(n)).collect()
    }

    fn apply_action(&mut self, state: &mut State<'tcx>, action: &PcgAction<'tcx>) {
        tracing::debug!(
            target: "pcg::holders",
            "{} action: {}",
            self.at,
            action.debug_line(self.ctxt)
        );
        let PcgAction::Borrow(action) = action else {
            // Owned actions do not change the borrow graph; the regain of a
            // loaned capability reports its renames in a label action after it.
            return;
        };
        let full_before = state.full.clone();
        let before = state.graph.nodes();
        let mut renamed_to = HashSet::new();
        match &action.kind {
            BorrowPcgActionKind::LabelLifetimeProjection(label) => {
                renamed_to = self.rename(state, label.renamed_nodes());
            }
            BorrowPcgActionKind::LabelPlace(label) => {
                renamed_to = self.rename(state, label.renamed_nodes());
            }
            BorrowPcgActionKind::Restore(restore) => {
                renamed_to = self.rename(state, restore.renamed_nodes());
            }
            BorrowPcgActionKind::Weaken(_) => {}
            BorrowPcgActionKind::AddEdge { edge } => {
                let edge = Edge::new(edge.kind(), self.ctxt);
                // A lifetime projection outside the graph holds its contents
                // as part of its place; an edge that brings it in as a source
                // brings them along (rule 5).
                if !edge.class.is_future() {
                    for s in &edge.sources {
                        if self.is_tracked(*s) && !is_future(*s) && !before.contains(s) {
                            state.full.insert(*s);
                        }
                    }
                }
                // The sources are not created full again after the transfer.
                renamed_to.extend(edge.sources.iter().copied());
                state.graph.edges.insert(edge.clone());
                self.on_add(state, &edge);
            }
            BorrowPcgActionKind::RemoveEdge(edge) => {
                self.remove(state, edge);
            }
        }
        self.after_change(state, &before, &renamed_to);
        if tracing::enabled!(target: "pcg::holders", tracing::Level::DEBUG) {
            for n in state.full.difference(&full_before) {
                tracing::debug!(target: "pcg::holders", "  +full {}", self.show(*n));
            }
            for n in full_before.difference(&state.full) {
                tracing::debug!(target: "pcg::holders", "  -full {}", self.show(*n));
            }
        }
    }

    /// Rules 5 and 6, applied after every change of the graph.
    fn after_change(
        &mut self,
        state: &mut State<'tcx>,
        before: &HashSet<Node<'tcx>>,
        renamed_to: &HashSet<Node<'tcx>>,
    ) {
        for n in state.graph.nodes() {
            if !before.contains(&n)
                && !renamed_to.contains(&n)
                && self.is_tracked(n)
                && !is_future(n)
                && !is_labelled(n)
                && !state.graph.has_incoming(n)
                && state.graph.in_non_future_edge(n)
            {
                state.full.insert(n);
            }
        }
        let emptied = state
            .graph
            .edges
            .iter()
            .filter(|e| matches!(e.class, EdgeClass::Deref))
            .filter(|e| e.targets.iter().any(|t| !is_lp(*t)))
            .flat_map(|e| e.sources.iter().copied())
            .filter(|s| self.is_tracked(*s) && state.full.contains(s))
            .collect::<Vec<_>>();
        for s in emptied {
            state.full.remove(&s);
            state.spent.insert(s);
        }
    }

    fn rename(
        &mut self,
        state: &mut State<'tcx>,
        renamed: &[NodeReplacement<'tcx>],
    ) -> HashSet<Node<'tcx>> {
        let renames: HashMap<Node<'tcx>, Node<'tcx>> =
            renamed.iter().map(|r| (r.from(), r.to())).collect();
        // A fixed order: when the future nodes of two lenders become current
        // in one action and share a giver, the first one takes from it.
        let mut ordered = renames.iter().map(|(f, t)| (*f, *t)).collect::<Vec<_>>();
        ordered.sort_by_cached_key(|(f, t)| (self.show(*f), self.show(*t)));
        for (from, to) in &renames {
            tracing::debug!(
                target: "pcg::holders",
                "  rename {} -> {}",
                self.show(*from),
                self.show(*to)
            );
        }
        if renames.is_empty() {
            return HashSet::new();
        }
        let old = state.graph.clone();
        state.graph.rename(&renames);
        // Future nodes that become current take from the sources of the
        // future edges into them (rule 2).
        for (from, to) in &ordered {
            if !is_future(*from) || is_future(*to) || !self.is_tracked(*to) {
                continue;
            }
            let into_from = old
                .edges
                .iter()
                .filter(|e| e.targets.contains(from))
                .map(|e| e.renamed(&renames))
                .collect::<Vec<_>>();
            let sources = |want_self: bool| {
                into_from
                    .iter()
                    .filter(|e| {
                        matches!(
                            e.class,
                            EdgeClass::Future(FutureClass::FromBorrow | FutureClass::FromExpansion)
                        ) != want_self
                            && e.class.is_future()
                    })
                    .flat_map(|e| e.sources.iter().copied())
                    .collect::<HashSet<_>>()
            };
            let selves = sources(true);
            // A future node of an earlier version of a place is never made
            // current by a restore: what flows into it passes on to the node
            // it leads into. Its givers are taken from instead (transit).
            let renamed_old = old.renamed(&renames);
            let mut givers: HashSet<Node<'tcx>> = HashSet::default();
            let mut visited: HashSet<Node<'tcx>> = HashSet::default();
            let mut todo = sources(false).into_iter().collect::<Vec<_>>();
            while let Some(g) = todo.pop() {
                if !visited.insert(g) {
                    continue;
                }
                if is_future(g) && has_labelled_base(g) {
                    todo.extend(
                        renamed_old
                            .edges
                            .iter()
                            .filter(|e| {
                                matches!(
                                    e.class,
                                    EdgeClass::Future(
                                        FutureClass::FromBorrow | FutureClass::FromExpansion
                                    )
                                ) && e.targets.contains(&g)
                            })
                            .flat_map(|e| e.sources.iter().copied()),
                    );
                } else {
                    givers.insert(g);
                }
            }
            let full_givers = givers
                .iter()
                .copied()
                .filter(|g| state.full.contains(g))
                .collect::<Vec<_>>();
            if !full_givers.is_empty() {
                state.full.insert(*to);
                for g in full_givers {
                    state.full.remove(&g);
                    state.gave_to_future.insert(g);
                    state.gave_to_future_now.insert(g);
                }
            } else if givers.iter().any(|g| state.gave_to_future_now.contains(g)) {
                // A node can give to several lenders that become current in
                // one phase, e.g. the future nodes of two lifetimes of one
                // reborrowed place.
                state.full.insert(*to);
            } else if givers.iter().any(|g| !is_future(*g) && self.is_owned(*g)) {
                // A giver outside the tracked graph gives from outside.
                state.full.insert(*to);
            } else if !givers.is_empty() {
                self.report.rule_p_failures.push(json!({
                    "at": self.at,
                    "stmt": self.stmt,
                    "node": self.show(*to),
                    "sources": self.show_set(givers.iter().copied()),
                }));
            } else {
                let full_selves = selves
                    .iter()
                    .copied()
                    .filter(|g| state.full.contains(g))
                    .collect::<Vec<_>>();
                if !full_selves.is_empty() {
                    state.full.insert(*to);
                    for g in full_selves {
                        state.full.remove(&g);
                    }
                }
            }
        }
        // Fullness follows the other renamed nodes (rule 1).
        let mut moved_full = Vec::new();
        for (from, to) in &ordered {
            if is_future(*from) && !is_future(*to) {
                continue;
            }
            if state.full.remove(from) {
                moved_full.push(*to);
            }
            if state.spent.remove(from) {
                state.spent.insert(*to);
            }
            if state.gave.remove(from) {
                state.gave.insert(*to);
            }
            if state.gave_to_future.remove(from) {
                state.gave_to_future.insert(*to);
            }
            if state.gave_to_future_now.remove(from) {
                state.gave_to_future_now.insert(*to);
            }
            if state.lost.remove(from) {
                state.lost.insert(*to);
            }
        }
        state.full.extend(moved_full);
        renames.values().copied().collect()
    }

    fn on_add(&mut self, state: &mut State<'tcx>, edge: &Edge<'tcx>) {
        // A future edge records where contents will flow; adding one moves
        // nothing, also when its target is already current.
        if edge.class.is_future() || !edge.blocks() {
            return;
        }
        let targets = edge
            .targets
            .iter()
            .copied()
            .filter(|t| !is_future(*t))
            .collect::<Vec<_>>();
        let full_sources = edge
            .sources
            .iter()
            .copied()
            .filter(|s| self.is_tracked(*s) && state.full.contains(s))
            .collect::<Vec<_>>();
        let targets = targets
            .into_iter()
            .filter(|t| self.is_tracked(*t))
            .collect::<Vec<_>>();
        if edge.only_into_untracked(&|n| self.is_tracked(n)) {
            // A shared reborrow freezes the sources, which keep what they
            // hold.
            return;
        }
        if targets.is_empty() {
            // A lifetime projection passes what it holds on to places.
            for s in full_sources {
                state.full.remove(&s);
                state.spent.insert(s);
            }
            return;
        }
        let feeds = edge.class == EdgeClass::Const
            || edge
                .sources
                .iter()
                .any(|s| state.full.contains(s) || state.spent.contains(s) || self.is_owned(*s));
        if feeds {
            for s in full_sources {
                if !targets.contains(&s) {
                    state.full.remove(&s);
                    state.spent.insert(s);
                }
            }
            state.full.extend(targets);
        }
    }

    fn remove(&mut self, state: &mut State<'tcx>, edge: &BorrowPcgEdge<'tcx>) {
        let edge = Edge::new(edge.kind(), self.ctxt);
        if !state.graph.edges.remove(&edge) {
            self.report.unknown_removals.push(json!({
                "at": self.at,
                "stmt": self.stmt,
                "edge": edge.display(self.ctxt),
            }));
        }
        self.on_remove(state, &edge);
    }

    fn on_remove(&mut self, state: &mut State<'tcx>, edge: &Edge<'tcx>) {
        if edge.class.is_future() || edge.class == EdgeClass::Const || !edge.blocks() {
            return;
        }
        let tracked_sources = edge
            .sources
            .iter()
            .copied()
            .filter(|s| self.is_tracked(*s) && !is_future(*s))
            .collect::<Vec<_>>();
        if matches!(edge.class, EdgeClass::Outlives { equal: false }) {
            // Next to a mutable borrow, the borrow edge returns the contents.
            let blocked = state.graph.blocked();
            if edge.sources.iter().all(|s| blocked.contains(s)) {
                return;
            }
        }
        if edge
            .targets
            .iter()
            .filter(|t| !is_future(**t))
            .all(|t| self.is_owned(*t))
        {
            // What a projection passed on to places comes back from them.
            state.full.extend(tracked_sources);
            return;
        }
        let gives = edge
            .targets
            .iter()
            .any(|t| state.full.contains(t) || state.gave.contains(t));
        if gives {
            for t in &edge.targets {
                if state.full.remove(t) {
                    state.gave.insert(*t);
                }
            }
            state.full.extend(tracked_sources);
        }
    }

    fn tag_missing(&self, g: &Graph<'tcx>, n: Node<'tcx>) -> String {
        let ins = g
            .edges
            .iter()
            .filter(|e| e.targets.contains(&n))
            .map(|e| {
                let from_place = if e.sources.iter().any(|s| self.is_owned(*s)) {
                    "(from place)"
                } else {
                    ""
                };
                format!("{}{from_place}", e.class.name())
            })
            .collect::<BTreeSet<_>>();
        let outs = g
            .edges
            .iter()
            .filter(|e| e.sources.contains(&n) && !e.class.is_future())
            .map(|e| format!("{}->FUTURE", e.class.name()))
            .collect::<BTreeSet<_>>();
        let mut tag = String::new();
        if is_labelled(n) {
            tag.push_str("labelled ");
        }
        if !outs.is_empty() {
            tag.push_str(&format!(
                "out:{} ",
                outs.into_iter().collect::<Vec<_>>().join(",")
            ));
        }
        let ins = ins.into_iter().collect::<Vec<_>>();
        tag.push_str(&format!(
            "in:{}",
            if ins.is_empty() {
                "-".into()
            } else {
                ins.join(",")
            }
        ));
        tag
    }

    fn tag_extra(&self, g: &Graph<'tcx>, n: Node<'tcx>) -> String {
        let outs = g
            .edges
            .iter()
            .filter(|e| e.sources.contains(&n) && e.blocks())
            .map(|e| {
                let to_place = if e
                    .targets
                    .iter()
                    .any(|t| !is_future(*t) && self.is_owned(*t))
                {
                    "(to place)"
                } else {
                    ""
                };
                format!("{}{to_place}", e.class.name())
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        format!(
            "{}{}blocked by:{}",
            if is_labelled(n) { "labelled " } else { "" },
            if is_future(n) { "future " } else { "" },
            if outs.is_empty() {
                "-".into()
            } else {
                outs.join(",")
            }
        )
    }

    /// Compares the full nodes with the leaves of `actual` and resynchronises
    /// on a mismatch. Returns whether they matched.
    fn compare(
        &mut self,
        state: &mut State<'tcx>,
        actual: &Graph<'tcx>,
        start_leaves: Option<&HashSet<Node<'tcx>>>,
        phase: &str,
    ) -> bool {
        // Rule 7: a place without a value holds nothing in its lifetime
        // projections; what they held left with the value (e.g. the result's
        // to the caller at the return).
        let dropped = state
            .full
            .iter()
            .copied()
            .filter(|n| actual.has_no_value(*n))
            .collect::<Vec<_>>();
        if !dropped.is_empty() {
            for n in &dropped {
                state.full.remove(n);
            }
            let dropped = dropped;
            self.report.dropped_with_value.push(json!({
                "at": self.at,
                "phase": phase,
                "stmt": self.stmt,
                "stmt_kind": self.stmt_kind,
                "nodes": self.show_set(dropped.iter().copied()),
                "in_graph": self.show_set(
                    dropped.iter().copied().filter(|n| actual.nodes().contains(n))
                ),
            }));
        }
        let mut leaves = actual.leaves(&|n| self.is_tracked(n));
        // Rule 8: an output of a call that gave its contents back to its
        // lender through a future edge holds nothing, although it stays a
        // leaf of the call's edge (which the call's other outputs still need).
        state.gave_to_future.retain(|n| !state.full.contains(n));
        let emptied_outputs = leaves
            .iter()
            .copied()
            .filter(|n| state.gave_to_future.contains(n) && actual.is_call_output(*n))
            .collect::<Vec<_>>();
        for n in &emptied_outputs {
            leaves.remove(n);
            if state.reported_outputs.insert(*n) {
                self.report.emptied_call_outputs.push(json!({
                    "at": self.at,
                    "phase": phase,
                    "stmt": self.stmt,
                    "node": self.show(*n),
                }));
            }
        }
        let start_leaves = start_leaves.map(|start| {
            start
                .iter()
                .copied()
                .filter(|n| !emptied_outputs.contains(n))
                .collect::<HashSet<_>>()
        });
        let start_leaves = start_leaves.as_ref();
        let nodes = actual.nodes();
        // A lost predicate that is still blocked was reported already.
        state
            .lost
            .retain(|n| state.full.contains(n) && nodes.contains(n) && !leaves.contains(n));
        let in_graph = state
            .full
            .iter()
            .copied()
            .filter(|n| nodes.contains(n) && !state.lost.contains(n))
            .collect::<HashSet<_>>();
        if start_leaves.is_some_and(|s| *s == leaves) && in_graph == leaves {
            return true;
        }
        if start_leaves.is_some() {
            self.report.changed += 1;
        }
        let missing = leaves.difference(&in_graph).copied().collect::<Vec<_>>();
        let extra = in_graph.difference(&leaves).copied().collect::<Vec<_>>();
        if missing.is_empty() && extra.is_empty() {
            if start_leaves.is_some() {
                self.report.matched += 1;
            }
            return true;
        }
        let missing_tags = missing
            .iter()
            .map(|n| {
                let tag = self.tag_missing(actual, *n);
                let tag = if state.gave_to_future.contains(n) {
                    format!("gave to future, {tag}")
                } else {
                    tag
                };
                (self.show(*n), tag)
            })
            .collect::<Vec<_>>();
        let extra_tags = extra
            .iter()
            .map(|n| (self.show(*n), self.tag_extra(actual, *n)))
            .collect::<Vec<_>>();
        let signature = format!(
            "{} {} | missing: {} | extra: {}",
            self.stmt_kind,
            phase,
            missing_tags
                .iter()
                .map(|(_, t)| t.as_str())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join("; "),
            extra_tags
                .iter()
                .map(|(_, t)| t.as_str())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join("; "),
        );
        if tracing::enabled!(target: "pcg::holders", tracing::Level::DEBUG) {
            for e in &actual.edges {
                tracing::debug!(target: "pcg::holders", "  mismatch graph: {}", e.display(self.ctxt));
            }
            for n in &state.full {
                tracing::debug!(target: "pcg::holders", "  mismatch full: {}", self.show(*n));
            }
        }
        let near = actual
            .edges
            .iter()
            .filter(|e| {
                e.nodes()
                    .any(|n| missing.contains(&n) || extra.contains(&n))
            })
            .map(|e| e.display(self.ctxt))
            .collect::<Vec<_>>();
        self.report.mismatches.push(json!({
            "at": self.at,
            "phase": phase,
            "stmt": self.stmt,
            "signature": signature,
            "missing": missing_tags,
            "extra": extra_tags,
            "edges": near,
        }));
        // Resynchronise, so that one mismatch does not cause later ones: the
        // missing leaves are taken as full, and the lost predicates stay full
        // (a client following the actions still holds them) and are not
        // reported again while they stay blocked.
        state.full.extend(missing);
        state.lost.extend(extra);
        false
    }

    fn set_stmt(&mut self, body: &mir::Body<'tcx>, block: BasicBlock, index: usize) {
        let data = &body[block];
        if let Some(stmt) = data.statements.get(index) {
            self.stmt = format!("{stmt:?}");
            self.stmt_kind = match &stmt.kind {
                mir::StatementKind::Assign(box (_, rvalue)) => {
                    let rvalue_kind = match rvalue {
                        mir::Rvalue::Use(mir::Operand::Move(_), ..) => "Move",
                        mir::Rvalue::Use(mir::Operand::Copy(_), ..) => "Copy",
                        mir::Rvalue::Use(..) => "Const",
                        mir::Rvalue::Ref(_, kind, _) if kind.mutability().is_mut() => "RefMut",
                        mir::Rvalue::Ref(..) => "Ref",
                        mir::Rvalue::Aggregate(..) => "Aggregate",
                        mir::Rvalue::Cast(..) => "Cast",
                        mir::Rvalue::RawPtr(..) => "RawPtr",
                        mir::Rvalue::Discriminant(..) => "Discriminant",
                        _ => "Other",
                    };
                    let target = if let mir::StatementKind::Assign(box (place, _)) = &stmt.kind
                        && place.is_indirect()
                    {
                        "(*_)"
                    } else {
                        "_"
                    };
                    format!("{target} = {rvalue_kind}")
                }
                other => format!("{other:?}")
                    .split(['(', ' '])
                    .next()
                    .unwrap_or_default()
                    .to_owned(),
            };
        } else {
            let kind = &data.terminator().kind;
            self.stmt = format!("{kind:?}");
            self.stmt_kind = format!("TERM {}", kind.name());
        }
        self.at = format!("{block:?}[{index}]");
    }

    fn report_json(self, function: String) -> Value {
        let r = self.report;
        json!({
            "fn": function,
            "phases": r.phases,
            "changed": r.changed,
            "match": r.matched,
            "edges_checked": r.edges_checked,
            "edges_matched": r.edges_matched,
            "rule_p_failures": r.rule_p_failures,
            "mismatches": r.mismatches,
            "unknown_removals": r.unknown_removals,
            "dropped_with_value": r.dropped_with_value,
            "emptied_call_outputs": r.emptied_call_outputs,
        })
    }
}

/// Replays the actions of the PCG of a function and compares the holders of
/// contents with the leaves of the graph; see the module documentation.
pub fn replay<'tcx>(output: &mut PcgOutput<'_, 'tcx>) -> Value {
    let ctxt = output.ctxt();
    let body = ctxt.body();
    let function = ctxt.body_def_path_str();
    let mut replay = Replay {
        ctxt,
        mutable_loan: Default::default(),
        report: Report::default(),
        at: String::new(),
        stmt: String::new(),
        stmt_kind: String::new(),
    };
    // The full nodes on each edge of the control-flow graph, after the
    // edge's actions.
    #[allow(clippy::type_complexity)]
    let mut on_edge: BTreeMap<
        (BasicBlock, BasicBlock),
        (HashSet<Node<'_>>, HashSet<Node<'_>>, HashSet<Node<'_>>),
    > = BTreeMap::new();
    let rpo = body.basic_blocks.reverse_postorder().to_vec();
    let loop_heads = rpo
        .iter()
        .copied()
        .filter(|b| output.analysis().loop_analysis().loop_head_of(*b).is_some())
        .collect::<BTreeSet<_>>();
    // The places without a value on entry to each block, for the comparison
    // on the edges into it.
    let mut entry_without_value = BTreeMap::new();
    for block in &rpo {
        if let Ok(Some(pcg_block)) = output.get_all_for_bb(*block)
            && let Some(first) = pcg_block.statements.first()
        {
            entry_without_value.insert(*block, without_value(&first.entry_state));
        }
    }
    for block in rpo {
        let Ok(Some(pcg_block)) = output.get_all_for_bb(block) else {
            continue;
        };
        let Some(first) = pcg_block.statements.first() else {
            continue;
        };
        let entry = Graph::of_state(&first.entry_state, ctxt);
        // A block starts with the full nodes of the edges into it if they all
        // agree (and none is a back edge not replayed yet), and with the
        // leaves of its graph otherwise.
        let preds = &body.basic_blocks.predecessors()[block];
        let incoming = preds
            .iter()
            .map(|p| on_edge.get(&(*p, block)))
            .collect::<Vec<_>>();
        let (full, lost) = match incoming.first() {
            Some(Some((first, _, lost)))
                if incoming
                    .iter()
                    .all(|s| s.is_some_and(|(full, _, _)| full == first)) =>
            {
                (first.clone(), lost.clone())
            }
            _ => (entry.leaves(&|n| replay.is_tracked(n)), HashSet::default()),
        };
        // The nodes that gave to a future node on some path into the block.
        let gave_to_future = incoming
            .iter()
            .flatten()
            .flat_map(|(_, gave, _)| gave.iter().copied())
            .collect();
        let mut state = State {
            graph: entry,
            full,
            gave_to_future,
            lost,
            ..State::default()
        };
        for (index, stmt) in pcg_block.statements.iter().enumerate() {
            replay.set_stmt(body, block, index);
            for phase in EvalStmtPhase::phases() {
                replay.report.phases += 1;
                state.spent.clear();
                state.gave_to_future_now.clear();
                state.gave_to_future_now.clear();
                state.gave.clear();
                // Each phase starts from the PCG's state before it; within the
                // phase, the graph changes only by the phase's actions.
                state.graph = Graph::of_state(
                    match phase.prev() {
                        None => &stmt.entry_state,
                        Some(prev) => &stmt.states[prev],
                    },
                    ctxt,
                );
                let start_leaves = state.graph.leaves(&|n| replay.is_tracked(n));
                for action in stmt.actions(phase).iter() {
                    replay.apply_action(&mut state, action);
                }
                let actual = Graph::of_state(&stmt.states[phase], ctxt);
                replay.compare(&mut state, &actual, Some(&start_leaves), &phase.to_string());
            }
        }
        if let Some(last) = pcg_block.statements.last() {
            state.graph = Graph::of_state(&last.states[EvalStmtPhase::last()], ctxt);
        }
        replay.at = format!("{block:?}[term]");
        let path_conditions = pcg_block
            .statements
            .last()
            .map(|last| {
                last.states[EvalStmtPhase::last()]
                    .borrow_pcg()
                    .validity_conditions
            })
            .unwrap_or(ValidityConditions::EMPTY);
        for succ in &pcg_block.terminator.succs {
            let mut state = state.clone();
            state.spent.clear();
            state.gave_to_future_now.clear();
            state.gave.clear();
            replay.at = format!("{block:?} -> {:?}", succ.block());
            for action in succ.actions().iter() {
                replay.apply_action(&mut state, action);
            }
            let actual = Graph::on_cfg_edge(
                succ.entry_graph(),
                entry_without_value
                    .get(&succ.block())
                    .cloned()
                    .unwrap_or_default(),
                path_conditions,
                block,
                succ.block(),
                ctxt,
            );
            // On an edge entering a loop head from outside the loop, a node
            // labelled before the join or at the loop head stands for its
            // place's value in the same state as the current node: the value
            // at the loop head, when the loop is entered.
            let (mut state, actual) =
                if loop_heads.contains(&succ.block()) && !ctxt.is_back_edge(block, succ.block()) {
                    let strip = |n: Node<'tcx>| strip_loop_labels(n, succ.block(), ctxt);
                    state.full = state.full.iter().map(|n| strip(*n)).collect();
                    state.gave_to_future = state.gave_to_future.iter().map(|n| strip(*n)).collect();
                    state.lost = state.lost.iter().map(|n| strip(*n)).collect();
                    let mut actual = actual;
                    actual.edges = actual
                        .edges
                        .iter()
                        .map(|e| Edge {
                            class: e.class,
                            sources: e.sources.iter().map(|n| strip(*n)).collect(),
                            targets: e.targets.iter().map(|n| strip(*n)).collect(),
                        })
                        .collect();
                    (state, actual)
                } else {
                    (state, actual)
                };
            replay.report.edges_checked += 1;
            if replay.compare(&mut state, &actual, None, "edge") {
                replay.report.edges_matched += 1;
            }
            on_edge.insert(
                (block, succ.block()),
                (state.full, state.gave_to_future, state.lost),
            );
        }
    }
    replay.report_json(function)
}
