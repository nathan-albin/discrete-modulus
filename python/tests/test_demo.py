"""
Tests for discrete_modulus.demo.
"""

from __future__ import annotations

import networkx as nx

from discrete_modulus import demo


def test_house_graph_structure():
    G, pos = demo.house_graph()
    assert G.number_of_nodes() == 5
    assert G.number_of_edges() == 6
    assert set(pos.keys()) == set(G.nodes())
    assert nx.is_connected(G)


def test_slashed_house_graph_structure():
    G, pos = demo.slashed_house_graph()
    assert G.number_of_nodes() == 5
    assert G.number_of_edges() == 7
    assert set(pos.keys()) == set(G.nodes())
    assert nx.is_connected(G)


def test_slashed_house_graph_is_house_graph_plus_one_edge():
    house, _ = demo.house_graph()
    slashed, _ = demo.slashed_house_graph()

    house_edges = {frozenset(e) for e in house.edges()}
    slashed_edges = {frozenset(e) for e in slashed.edges()}

    assert house_edges <= slashed_edges
    assert len(slashed_edges) == len(house_edges) + 1


def test_spanning_trees_count_matches_kirchhoff_theorem():
    G, _ = demo.house_graph()
    trees = list(demo.spanning_trees(G))
    assert len(trees) == round(nx.number_of_spanning_trees(G))


def test_spanning_trees_on_simple_cycle():
    # a cycle graph on n nodes has exactly n spanning trees (remove any one edge)
    G = nx.cycle_graph(5)
    trees = list(demo.spanning_trees(G))
    assert len(trees) == 5


def test_spanning_trees_are_all_valid_and_distinct():
    G, _ = demo.house_graph()
    n_nodes = G.number_of_nodes()

    seen = set()
    for tree_edges in demo.spanning_trees(G):
        assert len(tree_edges) == n_nodes - 1

        H = nx.Graph(tree_edges)
        assert nx.is_tree(H)
        assert set(H.nodes()) == set(G.nodes())

        key = frozenset(frozenset(e) for e in tree_edges)
        assert key not in seen
        seen.add(key)
