"""
Tests for discrete_modulus.families.networkx_families, checked against
plain networkx ground truth (independent of any modulus-specific
formulas), plus a regression test for a solver-noise bug found while
writing these tests.
"""

from __future__ import annotations

import networkx as nx
import numpy as np
import pytest
from helpers import edge_index

from discrete_modulus import demo
from discrete_modulus.algorithms import matrix_modulus, modulus
from discrete_modulus.families.networkx_families import (
    MinimumSpanningTree,
    ShortestConnectingPath,
)


def test_minimum_spanning_tree_matches_networkx_ground_truth():
    G, _ = demo.house_graph()
    idx = edge_index(G)
    m = G.number_of_edges()
    rho = np.random.default_rng(0).uniform(0.1, 10.0, size=m)  # distinct weights, avoid ties

    result = MinimumSpanningTree(G)(rho, 1e-3)

    H = G.copy()
    for u, v in H.edges():
        H[u][v]["w"] = rho[idx[frozenset((u, v))]]
    expected_weight = sum(d["w"] for _, _, d in nx.minimum_spanning_edges(H, weight="w", data=True))

    assert result.n.sum() == G.number_of_nodes() - 1  # a spanning tree has |V|-1 edges
    assert rho.dot(result.n) == pytest.approx(expected_weight)


def test_shortest_connecting_path_matches_networkx_ground_truth():
    G, _ = demo.house_graph()
    idx = edge_index(G)
    m = G.number_of_edges()
    rho = np.random.default_rng(0).uniform(0.1, 10.0, size=m)

    result = ShortestConnectingPath(G, [0], [3])(rho, 1e-3)

    H = G.copy()
    for u, v in H.edges():
        H[u][v]["w"] = rho[idx[frozenset((u, v))]]
    expected_length = nx.shortest_path_length(H, 0, 3, weight="w")

    assert rho.dot(result.n) == pytest.approx(expected_length)


def test_shortest_connecting_path_result_is_a_valid_path():
    G, _ = demo.house_graph()
    rho = np.ones(G.number_of_edges())

    result = ShortestConnectingPath(G, [0], [3])(rho, 1e-3)

    assert result.cons[0] == 0
    assert result.cons[-1] == 3
    for u, v in zip(result.cons, result.cons[1:], strict=False):
        assert G.has_edge(u, v)


def test_shortest_connecting_path_multi_source_multi_target():
    G, _ = demo.house_graph()
    rho = np.ones(G.number_of_edges())

    result = ShortestConnectingPath(G, [0, 1], [3, 4])(rho, 1e-3)

    assert result.cons[0] in (0, 1)
    assert result.cons[-1] in (3, 4)


@pytest.mark.parametrize("p", [1.0, 2.0, np.inf])
def test_modulus_does_not_crash_shortest_connecting_path_for_any_p(p):
    # Regression: matrix_modulus used to occasionally return rho with tiny
    # negative solver noise, which crashed ShortestConnectingPath's
    # Dijkstra call (negative edge weights aren't allowed).
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    result = modulus(
        m, matrix_modulus, ShortestConnectingPath(G, [0], [3]), p=p, tol=1e-6, max_iter=200
    )

    assert result.mod > 0
