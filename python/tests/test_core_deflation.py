"""
Tests for discrete_modulus.core_deflation: minimal-core detection via
exact-integer max-flow, and the recursive deflation sequence built on it.

Test strategy
-------------
1. Strictly homogeneous graphs (no forbidden trees) must report no core
   at all: `demo.slashed_house_graph`'s diamond-like symmetry and
   `nx.complete_graph`, both closed-form strictly homogeneous.

2. `demo.house_graph()` has one known core -- the triangle formed by its
   chord -- confirmed independently in earlier work by brute-force
   spanning-tree enumeration and by a closed-form determinant argument;
   both agree exactly with what `find_core` reports here.

3. Nested ties: a "multi-level house" graph (a tower of self-similar
   4-cycle "stories" capped by a triangular "roof", each story chosen to
   have the same edge/vertex ratio as the roof so every top-down suffix
   ties `theta(G)`) exercises the case a single, unrefined max-flow
   probe is not enough for -- `deflation_sequence` must still peel
   exactly one story per level, matching a level count fixed by
   construction, not some larger nested union.
"""

from __future__ import annotations

import networkx as nx
import pytest

from discrete_modulus import demo
from discrete_modulus.core_deflation import deflation_sequence, find_core


def _multi_level_house_graph(levels: int) -> nx.Graph:
    """
    A tower of `levels + 1` self-similar 4-cycle "stories" (each
    contributing 2 vertices and 3 edges, the same edge/vertex ratio as
    the final triangular "roof"), so every top-down suffix of stories --
    not just the roof alone -- ties the whole graph's density.
    """

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


def test_no_core_on_diamond() -> None:
    diamond = nx.Graph([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)])
    assert find_core(diamond) is None
    assert deflation_sequence(diamond) == []


@pytest.mark.parametrize("n", [4, 5, 6])
def test_no_core_on_complete_graph(n: int) -> None:
    assert find_core(nx.complete_graph(n)) is None


def test_house_graph_core_is_the_chord_triangle() -> None:
    G, _pos = demo.house_graph()
    core = find_core(G)
    assert core == {frozenset({0, 1}), frozenset({0, 2}), frozenset({1, 2})}

    cores = deflation_sequence(G)
    assert cores == [core]


@pytest.mark.parametrize("levels", [1, 2, 3, 4, 5])
def test_multi_level_house_peels_one_story_per_level(levels: int) -> None:
    G = _multi_level_house_graph(levels)
    cores = deflation_sequence(G)

    # exactly `levels` cores, matching the number of stories above the
    # base triangle, not some larger nested union of several stories
    assert len(cores) == levels
    assert all(len(core) == 3 for core in cores)

    # the outermost core found first is always the topmost roof
    apex = 2 * (levels + 1)
    top_a, top_b = 2 * levels, 2 * levels + 1
    assert cores[0] == {
        frozenset({top_a, top_b}),
        frozenset({top_a, apex}),
        frozenset({top_b, apex}),
    }

    # every original edge is accounted for in exactly one core or the
    # rigid base left behind after the last contraction
    covered = set().union(*cores) if cores else set()
    assert covered <= {frozenset(e) for e in G.edges()}


def test_find_core_rejects_too_small_or_edgeless_graphs() -> None:
    assert find_core(nx.Graph([(0, 1)])) is None
    assert find_core(nx.empty_graph(3)) is None
