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
//!    Without such sources, it takes the contents of its earlier version (the
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
    },
    pcg::{
        CapabilityKind, EvalStmtPhase, Pcg, PcgNode, place_capabilities::PlaceCapabilitiesReader,
    },
    rustc_interface::middle::mir::{self, BasicBlock},
    utils::{
        CompilerCtxt, Place,
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
fn is_owned(n: Node<'_>) -> bool {
    !is_lp(n) || is_remote(n) || is_const(n)
}

/// A lifetime projection whose contents the replay tracks.
fn is_tracked(n: Node<'_>) -> bool {
    is_lp(n) && !is_owned(n)
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

    fn has_incoming(&self, n: Node<'tcx>) -> bool {
        self.edges.iter().any(|e| e.targets.contains(&n))
    }

    /// Whether the node appears in an edge that is not a future edge.
    fn in_non_future_edge(&self, n: Node<'tcx>) -> bool {
        self.edges
            .iter()
            .any(|e| !e.class.is_future() && e.nodes().any(|m| m == n))
    }

    /// The nodes that hold their contents according to the graph's shape.
    fn leaves(&self) -> HashSet<Node<'tcx>> {
        let blocked = self.blocked();
        self.nodes()
            .into_iter()
            .filter(|n| {
                is_tracked(*n) && !is_future(*n) && !blocked.contains(n) && !self.has_no_value(*n)
            })
            .collect()
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
    /// Nodes that gave their contents back in the current phase.
    gave: HashSet<Node<'tcx>>,
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
}

struct Replay<'a, 'tcx> {
    ctxt: CompilerCtxt<'a, 'tcx>,
    report: Report,
    /// The location being replayed, for the report.
    at: String,
    stmt: String,
    stmt_kind: String,
}

impl<'a, 'tcx> Replay<'a, 'tcx> {
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
                        if is_tracked(*s) && !is_future(*s) && !before.contains(s) {
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
                && is_tracked(n)
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
            .filter(|s| is_tracked(*s) && state.full.contains(s))
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
        for (from, to) in &renames {
            if !is_future(*from) || is_future(*to) {
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
            let givers = sources(false);
            let selves = sources(true);
            let full_givers = givers
                .iter()
                .copied()
                .filter(|g| state.full.contains(g))
                .collect::<Vec<_>>();
            if !full_givers.is_empty() {
                state.full.insert(*to);
                for g in full_givers {
                    state.full.remove(&g);
                }
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
        for (from, to) in &renames {
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
            .filter(|s| is_tracked(*s) && state.full.contains(s))
            .collect::<Vec<_>>();
        if targets.iter().any(|t| is_owned(*t)) {
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
                .any(|s| state.full.contains(s) || state.spent.contains(s) || is_owned(*s));
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
            .filter(|s| is_tracked(*s) && !is_future(*s))
            .collect::<Vec<_>>();
        if matches!(edge.class, EdgeClass::Outlives { equal: false }) {
            // Next to a mutable borrow, the borrow edge returns the contents.
            let blocked = state.graph.blocked();
            if edge.sources.iter().all(|s| blocked.contains(s)) {
                return;
            }
        }
        if edge.targets.iter().any(|t| !is_future(*t) && is_owned(*t)) {
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
                let from_place = if e.sources.iter().any(|s| is_owned(*s)) {
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
                let to_place = if e.targets.iter().any(|t| !is_future(*t) && is_owned(*t)) {
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
        let leaves = actual.leaves();
        let nodes = actual.nodes();
        let in_graph = state
            .full
            .iter()
            .copied()
            .filter(|n| nodes.contains(n))
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
            .map(|n| (self.show(*n), self.tag_missing(actual, *n)))
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
        // Resynchronise, so that one mismatch does not cause later ones.
        state.full.retain(|n| !nodes.contains(n));
        state.full.extend(leaves);
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
        })
    }
}

/// Replays the actions of the PCG of a function and compares the holders of
/// contents with the leaves of the graph; see the module documentation.
pub fn replay(output: &mut PcgOutput<'_, '_>) -> Value {
    let ctxt = output.ctxt();
    let body = ctxt.body();
    let function = ctxt.body_def_path_str();
    let mut replay = Replay {
        ctxt,
        report: Report::default(),
        at: String::new(),
        stmt: String::new(),
        stmt_kind: String::new(),
    };
    // The full nodes on each edge of the control-flow graph, after the
    // edge's actions.
    let mut on_edge: BTreeMap<(BasicBlock, BasicBlock), HashSet<Node<'_>>> = BTreeMap::new();
    let rpo = body.basic_blocks.reverse_postorder().to_vec();
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
        let full = match incoming.first() {
            Some(Some(first)) if incoming.iter().all(|s| *s == Some(*first)) => (*first).clone(),
            _ => entry.leaves(),
        };
        let mut state = State {
            graph: entry,
            full,
            ..State::default()
        };
        for (index, stmt) in pcg_block.statements.iter().enumerate() {
            replay.set_stmt(body, block, index);
            for phase in EvalStmtPhase::phases() {
                replay.report.phases += 1;
                state.spent.clear();
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
                let start_leaves = state.graph.leaves();
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
        for succ in &pcg_block.terminator.succs {
            let mut state = state.clone();
            state.spent.clear();
            state.gave.clear();
            replay.at = format!("{block:?} -> {:?}", succ.block());
            for action in succ.actions().iter() {
                replay.apply_action(&mut state, action);
            }
            let actual = Graph::of(
                succ.entry_graph(),
                entry_without_value
                    .get(&succ.block())
                    .cloned()
                    .unwrap_or_default(),
                ctxt,
            );
            replay.report.edges_checked += 1;
            if replay.compare(&mut state, &actual, None, "edge") {
                replay.report.edges_matched += 1;
            }
            on_edge.insert((block, succ.block()), state.full);
        }
    }
    replay.report_json(function)
}
