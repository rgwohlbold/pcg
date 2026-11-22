//! Data structures and algorithms related to [`UnblockGraph`].
use std::marker::PhantomData;

use crate::{
    borrow_pcg::{
        borrow_pcg_edge::{BorrowPcgEdge, BorrowPcgEdgeRef},
        borrow_pcg_expansion::BorrowPcgExpansion,
        edge::{aggregate::AggregateEdge, kind::BorrowPcgEdgeKind},
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
        let mut edges = self.edges;
        let mut actions = vec![];

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
