"""
Tests for discrete_modulus.pmf_construction: the deflation-plus-Wolfe's-
algorithm per-round pmf construction.

Test strategy
-------------
1. Exact marginals on a strictly homogeneous graph (`nx.complete_graph`)
   where deflation finds no core at all, so the whole thing reduces to a
   single call to `min_norm_point_wolfe` -- the baseline case.

2. Exact marginals on `demo.house_graph()`, which has one known core
   (the chord triangle, see `test_core_deflation.py`) -- exercises the
   actual deflation-into-two-pieces path, and checks that gluing pieces
   back together via edge provenance reproduces the correct uniform
   marginal (2/3 on every edge, since `theta = (5-1)/6`).

3. Nested ties on a multi-level house graph (parametrized over several
   levels), checking exact marginals and that every sampled tree is a
   genuine spanning tree of the original graph -- end-to-end validation
   of the provenance bookkeeping through several contractions, not just
   a single one.

4. A genuine MultiGraph input (parallel edges, the shape of a real
   solver-dispatched shrunk multigraph) -- checks the whole pipeline
   (core detection, contraction, MinimumSpanningTree, provenance) stays
   correct once parallel edges are actually in play, not just tested
   piecemeal in each module's own tests.
"""

from __future__ import annotations

import random
from fractions import Fraction

import networkx as nx
import pytest

from discrete_modulus import demo
from discrete_modulus.pmf_construction import build_factored_pmf


def _multi_level_house_graph(levels: int) -> nx.Graph:
    G: nx.Graph = nx.Graph()
    for i in range(levels + 1):
        a, b = 2 * i, 2 * i + 1
        G.add_edge(a, b)
        if i > 0:
            G.add_edge(a - 2, a)
            G.add_edge(b - 2, b)
    apex = 2 * (levels + 1)
    top_a, top_b = 2 * levels, 2 * levels + 1
    G.add_edge(top_a, apex)
    G.add_edge(top_b, apex)
    return G


def _assert_exact_uniform_marginal(G: nx.Graph, pmf) -> None:
    n = G.number_of_nodes()
    m = G.number_of_edges()
    theta = Fraction(n - 1, m)

    for piece in pmf.pieces:
        assert sum(entry.weight for entry in piece.result.support) == Fraction(1)

    eta = pmf.marginal()
    assert len(eta) == m
    assert all(v == theta for v in eta)


def _assert_samples_are_spanning_trees(
    G: nx.Graph, pmf, n_samples: int = 50, seed: int = 0
) -> None:
    rng = random.Random(seed)
    edges = list(G.edges())
    for _ in range(n_samples):
        tree = pmf.sample(rng)
        assert len(tree) == G.number_of_nodes() - 1
        # a MultiGraph reconstruction (regardless of G's own type) avoids
        # accidentally collapsing two distinct sampled edge indices that
        # happen to share the same vertex pair
        H: nx.MultiGraph = nx.MultiGraph()
        H.add_nodes_from(G.nodes())
        H.add_edges_from(edges[i] for i in tree)
        assert H.number_of_edges() == len(tree)
        assert nx.is_connected(H)


def test_strictly_homogeneous_graph_is_a_single_piece() -> None:
    G = nx.complete_graph(4)
    pmf = build_factored_pmf(G)

    assert len(pmf.pieces) == 1
    _assert_exact_uniform_marginal(G, pmf)
    _assert_samples_are_spanning_trees(G, pmf)


def test_house_graph_deflates_into_two_pieces() -> None:
    G, _pos = demo.house_graph()
    pmf = build_factored_pmf(G, verbose=False)

    assert len(pmf.pieces) == 2
    assert all(piece.graph.number_of_nodes() == 3 for piece in pmf.pieces)
    _assert_exact_uniform_marginal(G, pmf)
    _assert_samples_are_spanning_trees(G, pmf)


@pytest.mark.parametrize("levels", [1, 2, 3, 4])
def test_multi_level_house_graph_exact_marginals(levels: int) -> None:
    G = _multi_level_house_graph(levels)
    pmf = build_factored_pmf(G)

    assert len(pmf.pieces) == levels + 1  # `levels` cores plus the rigid base
    _assert_exact_uniform_marginal(G, pmf)
    _assert_samples_are_spanning_trees(G, pmf, n_samples=30)


def test_multigraph_shrunk_graph_exact_marginals() -> None:
    # A genuine multigraph, built by uniformly doubling every edge of
    # the house graph -- the shape a real contracted round can produce.
    # Doubling *uniformly* preserves every relative density exactly (so
    # the graph stays homogeneous with the same {0, 1, 2} core), unlike
    # doubling a single arbitrary edge, which can make that edge's
    # endpoints strictly denser than the whole graph and so isn't a
    # valid homogeneous input in the first place.
    G, _pos = demo.house_graph()
    MG: nx.MultiGraph = nx.MultiGraph()
    for u, v in G.edges():
        MG.add_edge(u, v)
        MG.add_edge(u, v)

    pmf = build_factored_pmf(MG)
    _assert_exact_uniform_marginal(MG, pmf)
    _assert_samples_are_spanning_trees(MG, pmf)
