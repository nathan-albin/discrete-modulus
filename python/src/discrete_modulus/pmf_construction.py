"""
Builds an exact pmf on spanning trees of a homogeneous shrunk
(multi)graph -- a graph for which some prescribed marginal (typically
uniform) is known to be achievable, as it would be for a component the
spanning-tree-modulus solver dispatches for a single round.

Rather than running `min_norm_point.min_norm_point_wolfe` once on the
whole shrunk graph, this first deflates it (`core_deflation`) into a
rigid base plus a sequence of cores, each strictly homogeneous by
construction (once a core is peeled away, the piece left behind can
never have a further forbidden tree -- see `core_deflation`'s module
docstring). Wolfe's algorithm then only ever sees small, strictly
homogeneous pieces -- exactly its validated regime (a cold start on the
house graph converges in 3 major iterations) -- so there is no need to
detect or recover from the failure mode (unbounded active-set growth
chasing a degenerate/forbidden-tree marginal) that motivated deflating
in the first place.

The result is a *factored* pmf: one independent local pmf per piece,
plus each piece's edge provenance back to the original graph, rather
than a flat list of (spanning tree of G, weight) pairs. Picking a
spanning tree of `G` is "independently sample one local tree from each
piece's own pmf, then take the union of the pre-images of the edges
collected" -- correct because the pieces partition `G`'s edges (each
core's edges are disjoint from the rest, sharing only attachment
vertices, and the final rigid base gets whatever edges no core ever
claimed), so combining independently-valid local choices can never
create a cycle, and marginals are correct because they're already exact
on each piece. This avoids ever materializing the flat product (which
blows up as (local piece size)^(number of pieces), intractable for
deeply-nested inputs) at the cost of any downstream consumer needing to
understand this factored structure rather than a flat tree list --
that tradeoff isn't resolved here, only the pmf construction itself.
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction

import networkx as nx
import numpy as np

from .core_deflation import find_core
from .protocols import ExactArray, MinNormPointResult
from .tree_packing import build_tree_packing


@dataclass(frozen=True)
class LocalPiece:
    """
    One deflation piece (the rigid base, or one core) together with its
    exact local pmf.

    Attributes
    ----------
    graph : networkx graph
        The piece's own induced (multi)subgraph, as passed to
        `min_norm_point_wolfe` (via `MinimumSpanningTree`).

    provenance : list of int
        Maps a local edge index (this piece's own `MinimumSpanningTree`
        enumeration, i.e. `graph.edges(data=True)` order) to the
        corresponding edge's index in the *original* graph passed to
        `build_factored_pmf`.

    result : MinNormPointResult
        Wolfe's algorithm's result on `graph`: `result.support` is the
        piece's local pmf (`SupportEntry.n` in local-edge-index order,
        `SupportEntry.weight` its exact probability).
    """

    graph: nx.Graph
    provenance: list[int]
    result: MinNormPointResult


@dataclass(frozen=True)
class FactoredPmf:
    """
    An exact pmf on spanning trees of a graph with `m` edges, factored
    as a list of independent `LocalPiece`s (see module docstring).
    """

    m: int
    pieces: list[LocalPiece]

    def sample(self, rng: random.Random) -> frozenset:
        """
        Draws one spanning tree from the pmf: independently samples a
        local tree from each piece (weighted by its exact probability)
        and unions the pre-images of the edges collected, each as an
        index into the original graph's edges.
        """

        chosen: set[int] = set()
        for piece in self.pieces:
            weights = [float(entry.weight) for entry in piece.result.support]
            (entry,) = rng.choices(piece.result.support, weights=weights, k=1)
            for local_i, orig_i in enumerate(piece.provenance):
                if entry.n[local_i]:
                    chosen.add(orig_i)
        return frozenset(chosen)

    def marginal(self) -> ExactArray:
        """
        The pmf's exact expected usage vector (eta), indexed by the
        original graph's edges -- `eta[i]` is the exact probability that
        edge `i` is included in a sampled spanning tree.
        """

        eta: ExactArray = np.array([Fraction(0)] * self.m, dtype=object)
        for piece in self.pieces:
            for entry in piece.result.support:
                for local_i, orig_i in enumerate(piece.provenance):
                    if entry.n[local_i]:
                        eta[orig_i] += entry.weight
        return eta


def build_factored_pmf(G: nx.Graph, verbose: bool = False) -> FactoredPmf:
    """
    Builds a `FactoredPmf` on spanning trees of a homogeneous
    (multi)graph `G` (the shape of a shrunk multigraph the solver
    dispatches to a single round).

    Parameters
    ----------
    G : networkx graph or multigraph
        A connected, homogeneous graph -- see `core_deflation.find_core`.

    verbose : bool
        If True, prints each deflation level's piece size as it's
        solved.

    Returns
    -------
    FactoredPmf
    """

    m = G.number_of_edges()
    working = G.copy()

    # Tag every edge with its index in the ORIGINAL graph before any
    # deflation happens. nx.contracted_nodes preserves each surviving
    # edge's own attribute dict untouched (parallel edges never merge,
    # for either Graph or MultiGraph), so this identity survives however
    # many contractions follow, unlike trying to recover it after the
    # fact from vertex labels alone (contracted vertices get synthetic
    # names with no relation to G's originals).
    for i, (_u, _v, data) in enumerate(working.edges(data=True)):
        data["orig"] = i

    pieces: list[LocalPiece] = []
    level = 0
    while True:
        core_vertices = find_core(working)
        if core_vertices is None:
            pieces.append(_solve_piece(working))
            if verbose:
                print(
                    f"level {level}: rigid base, {working.number_of_nodes()} vertices, "
                    f"{working.number_of_edges()} edges"
                )
            break

        piece_graph = working.subgraph(core_vertices).copy()
        pieces.append(_solve_piece(piece_graph))
        if verbose:
            print(
                f"level {level}: core with {piece_graph.number_of_nodes()} vertices, "
                f"{piece_graph.number_of_edges()} edges"
            )

        new_point = f"__core_{level}__"
        contracted = working
        core_list = list(core_vertices)
        for v in core_list[1:]:
            contracted = nx.contracted_nodes(contracted, core_list[0], v, self_loops=False)
        working = nx.relabel_nodes(contracted, {core_list[0]: new_point})

        level += 1
        if level > working.number_of_nodes() + m:
            raise RuntimeError("deflation did not terminate")

    return FactoredPmf(m=m, pieces=pieces)


def _solve_piece(piece_graph: nx.Graph) -> LocalPiece:
    # `piece_graph` is strictly homogeneous by construction (the caller
    # only ever hands this a rigid base or a core -- see the module
    # docstring), so its own min-norm point is known in closed form:
    # theta = (n-1)/m, uniform on every edge. `build_tree_packing`
    # constructs that exact pmf directly (see its own module docstring
    # for why this replaced `min_norm_point_wolfe` here: every piece
    # this function ever sees is exactly packing's use case, and
    # packing's cost is bounded in a way Wolfe's active-set growth
    # isn't).
    n_piece = piece_graph.number_of_nodes()
    m_piece = piece_graph.number_of_edges()
    theta = Fraction(n_piece - 1, m_piece)
    result = build_tree_packing(piece_graph, p=theta.numerator, q=theta.denominator)
    if result is None:
        raise RuntimeError(
            f"tree packing did not converge on a piece with {n_piece} vertices, "
            f"{m_piece} edges, theta={theta}"
        )
    provenance = [data["orig"] for _, _, data in piece_graph.edges(data=True)]
    return LocalPiece(graph=piece_graph, provenance=provenance, result=result)
