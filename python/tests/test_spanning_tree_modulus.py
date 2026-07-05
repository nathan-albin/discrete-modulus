"""
Tests for discrete_modulus.spanning_tree_modulus: Cunningham's algorithm.

Test strategy
-------------
1. `rank`: hand-verified values on `demo.house_graph()`, mirroring the
   companion notebook's worked example.

2. `EdgeFunction`: the `x(u,v) == x(v,u)` symmetry and zero-initialization.

3. Analytic cases with closed-form values:
   - The exact worked example from the companion notebook (a 6-cycle plus
     one chord): `graph_vulnerability` gives theta = 3/4, and
     `cunningham_min(G, F, 3, 4)` gives a specific P(qf)-basis.
   - `spanning_tree_modulus` on complete graphs K_n: eta* = 2/n on every
     edge (a known closed form for spanning tree "strength").
   - `demo.house_graph()` / `demo.slashed_house_graph()`: uniform eta*
     values, by symmetry.

4. Structural invariants that must hold for any graph, checked on a
   handful of random connected graphs:
   - every edge gets an eta* value, and every value lies in (0, 1].
   - `spanning_tree_modulus` on a disconnected graph agrees, edge by edge,
     with running it independently on each connected component.

5. A regression case (`disjoint_union(barbell_graph(4, 0), cycle_graph(3))`)
   that exercises the rare "entire edge set is tight, rerunning" branch on
   a component that is a strict subgraph of the input -- this used to
   raise `KeyError` from a bug that reused the wrong graph object in that
   branch.
"""

from __future__ import annotations

from fractions import Fraction

import networkx as nx
import pytest

from discrete_modulus import demo
from discrete_modulus.spanning_tree_modulus import (
    EdgeFunction,
    create_flow_graph,
    cunningham_min,
    graph_vulnerability,
    rank,
    spanning_tree_modulus,
)

# ---------------------------------------------------------------------
# rank
# ---------------------------------------------------------------------


@pytest.mark.parametrize(
    ("edges", "expected"),
    [
        ([], 0),
        ([(0, 1)], 1),
        ([(0, 1), (1, 2)], 2),
        ([(0, 2), (3, 4)], 2),
        ([(0, 1), (1, 2), (2, 0)], 2),
    ],
)
def test_rank_on_edge_subsets(edges, expected):
    G, _ = demo.house_graph()
    assert rank(G, edges) == expected


def test_rank_of_full_edge_set_is_n_minus_1_for_connected_graph():
    G, _ = demo.house_graph()
    assert rank(G, list(G.edges)) == len(G.nodes) - 1


# ---------------------------------------------------------------------
# EdgeFunction
# ---------------------------------------------------------------------


def test_edge_function_initializes_to_zero_on_every_edge():
    G, _ = demo.house_graph()
    ef = EdgeFunction(G)
    assert set(ef.keys()) == {frozenset(e) for e in G.edges}
    assert all(v == 0 for v in ef.values())


def test_edge_function_is_symmetric():
    G, _ = demo.house_graph()
    ef = EdgeFunction(G)
    u, v = next(iter(G.edges))
    ef[(u, v)] = 5
    assert ef[(v, u)] == 5


def test_edge_function_str_reports_every_edge():
    G, _ = demo.house_graph()
    ef = EdgeFunction(G)
    rendered = str(ef)
    assert rendered.count(":") == len(G.edges)


# ---------------------------------------------------------------------
# Analytic cases
# ---------------------------------------------------------------------


def test_notebook_worked_example():
    # 6-cycle plus one chord, as in the companion notebook
    G = nx.cycle_graph(6)
    G.add_edge(0, 2)
    F = create_flow_graph(G)

    x, tight = cunningham_min(G, F, 3, 4)

    # every edge gets 3 except {1, 2}, which gets 2 (i.e. 3/4 and 2/4=1/2
    # once divided by q=4)
    assert x[(1, 2)] == 2
    assert all(x[e] == 3 for e in G.edges if frozenset(e) != frozenset((1, 2)))

    # the triangle {0, 1, 2} is the tight set
    assert {frozenset(e) for e in tight} == {
        frozenset((0, 1)),
        frozenset((1, 2)),
        frozenset((0, 2)),
    }

    theta, _ = graph_vulnerability(G, F)
    assert theta == Fraction(3, 4)


@pytest.mark.parametrize("n", [3, 4, 5, 6, 7])
def test_complete_graph_eta_star_is_two_over_n(n):
    G = nx.complete_graph(n)
    eta = spanning_tree_modulus(G)
    assert set(eta.values()) == {Fraction(2, n)}


def test_spanning_tree_modulus_verbose_prints_progress_table(capsys):
    G, _ = demo.house_graph()
    spanning_tree_modulus(G, verbose=True)

    out = capsys.readouterr().out
    assert "eta" in out
    assert "comp remain" in out


def test_house_graph_eta_star_is_uniform():
    G, _ = demo.house_graph()
    eta = spanning_tree_modulus(G)
    assert set(eta.values()) == {Fraction(2, 3)}


def test_slashed_house_graph_eta_star_is_uniform():
    G, _ = demo.slashed_house_graph()
    eta = spanning_tree_modulus(G)
    assert set(eta.values()) == {Fraction(4, 7)}


# ---------------------------------------------------------------------
# Structural invariants
# ---------------------------------------------------------------------


@pytest.mark.parametrize("seed", range(5))
@pytest.mark.filterwarnings("ignore:Got entire edge set as tight")
def test_eta_star_covers_every_edge_with_value_in_zero_one(seed):
    G = nx.gnm_random_graph(8, 12, seed=seed)
    if not nx.is_connected(G):
        pytest.skip("random graph not connected for this seed")

    eta = spanning_tree_modulus(G)

    assert set(eta.keys()) == {frozenset(e) for e in G.edges}
    assert all(0 < v <= 1 for v in eta.values())


def test_disconnected_graph_matches_per_component_computation():
    G1 = nx.cycle_graph(3)
    G2 = nx.wheel_graph(5)
    G = nx.disjoint_union(G1, G2)

    eta_combined = spanning_tree_modulus(G)
    eta1 = spanning_tree_modulus(G1)
    eta2 = spanning_tree_modulus(G2)

    n1 = G1.number_of_nodes()
    for u, v in G1.edges:
        assert eta_combined[(u, v)] == eta1[(u, v)]
    for u, v in G2.edges:
        assert eta_combined[(u + n1, v + n1)] == eta2[(u, v)]


# ---------------------------------------------------------------------
# Regression: "entire edge set is tight" fallback on a strict subgraph
# ---------------------------------------------------------------------


def test_entire_edge_set_tight_fallback_on_disconnected_graph():
    # barbell_graph(4, 0): two K4s joined by a single bridge edge. Alongside
    # a disjoint triangle, the barbell component is a strict subgraph of
    # the full input when it's processed, which used to trigger a
    # KeyError (the fallback branch looked up capacities, meant for the
    # component being processed, on the wrong graph).
    G = nx.disjoint_union(nx.barbell_graph(4, 0), nx.cycle_graph(3))

    with pytest.warns(UserWarning, match="entire edge set"):
        eta = spanning_tree_modulus(G)

    assert set(eta.values()) == {Fraction(1, 2), Fraction(2, 3), Fraction(1, 1)}
