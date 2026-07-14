"""
Tests for discrete_modulus.min_norm_point: away-step Frank-Wolfe (AFW) and
Wolfe's (1976) minimum-norm-point algorithm.

Test strategy
-------------
1. Cold-start convergence to the correct, exact marginals, on two graphs
   with different symmetry (`demo.house_graph()`, `nx.complete_graph(4)`),
   parametrized over both algorithms.

2. Support correctness: the pmf's support must avoid the two spanning
   trees of `demo.house_graph()` that no feasible uniform-marginal pmf can
   place any weight on. The forbidden set is derived independently of the
   algorithms under test, via a small `scipy.optimize.linprog` feasibility
   check over all 11 spanning trees (`demo.spanning_trees`) -- not by
   reusing the specific edge tuples from `scratch/wolfe_min_norm*.py`,
   whose example graph labels its chord differently from
   `demo.house_graph()`.

3. The away-step/eviction mechanism: seeding the active set with one of
   the forbidden trees and confirming it gets removed. **Wolfe's
   algorithm only** -- while implementing this module, seeding AFW with a
   deliberately bad start was found to blow up to 50+ digit exact
   `Fraction` denominators within about 7 iterations with no sign of
   converging (see `min_norm_point_afw`'s docstring "Notes"); AFW's cold
   start (tested above) stays cheap, but the multi-corrective-step
   scenario needed to exercise its drop-step mechanism isn't practical to
   run in exact arithmetic. This is itself a validated property of AFW,
   not a gap in test coverage.

4. Failure/reporting paths: both algorithms' non-convergence `RuntimeError`
   (including Wolfe's minor-cycle-specific one), and `verbose=True`'s
   printed output. These are cheap to cover directly (a `max_iter`/
   `max_major`/`max_minor` of 0 always fails immediately, regardless of
   the graph) and don't run into AFW's blowup problem, unlike (3).
   AFW's away-branch-specific verbose output (the "removed" print, only
   reached together with the away-step code itself) is not covered, for
   the same reason as (3).
"""

from __future__ import annotations

from fractions import Fraction

import networkx as nx
import numpy as np
import pytest
from helpers import edge_index
from scipy.optimize import linprog

from discrete_modulus import demo
from discrete_modulus.families.networkx_families import MinimumSpanningTree
from discrete_modulus.min_norm_point import min_norm_point_afw, min_norm_point_wolfe
from discrete_modulus.protocols import ExactArray

ALGORITHMS = [min_norm_point_afw, min_norm_point_wolfe]


def _tree_vector(tree: tuple, idx: dict[frozenset, int], m: int) -> ExactArray:
    n = np.array([Fraction(0)] * m, dtype=object)
    for e in tree:
        n[idx[frozenset(e)]] = Fraction(1)
    return n


def _ground_truth_forbidden_trees(G: nx.Graph, theta: Fraction) -> set[frozenset]:
    """
    Independently (not using `min_norm_point`) determines which spanning
    trees of `G` can never appear with positive weight in any feasible
    pmf achieving uniform marginal `theta` on every edge, via LP
    feasibility: for each tree T, maximize its weight subject to the
    marginal/sum-to-one constraints; T is forbidden iff that maximum is
    (numerically) zero.
    """

    idx = edge_index(G)
    m = G.number_of_edges()
    trees = list(demo.spanning_trees(G))

    usage = np.zeros((len(trees), m))
    for i, tree in enumerate(trees):
        for e in tree:
            usage[i, idx[frozenset(e)]] = 1.0

    A_eq = np.vstack([usage.T, np.ones((1, len(trees)))])
    b_eq = [float(theta)] * m + [1.0]

    forbidden = set()
    for j, tree in enumerate(trees):
        c = np.zeros(len(trees))
        c[j] = -1.0
        res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=(0, None))
        max_weight = -res.fun if res.success and res.fun is not None else 0.0
        if max_weight < 1e-7:
            forbidden.add(frozenset(frozenset(e) for e in tree))

    return forbidden


# ---------------------------------------------------------------------
# Cold-start convergence
# ---------------------------------------------------------------------


@pytest.mark.parametrize("min_norm_point", ALGORITHMS)
def test_house_graph_converges_to_uniform_marginals(min_norm_point):
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    result = min_norm_point(m, MinimumSpanningTree(G))

    assert all(v == Fraction(2, 3) for v in result.x)
    assert sum(e.weight for e in result.support) == 1
    assert all(e.weight > 0 for e in result.support)


@pytest.mark.parametrize("min_norm_point", ALGORITHMS)
def test_complete_graph_converges_to_uniform_marginals(min_norm_point):
    # K4: by vertex-transitivity the target marginal is exactly
    # (n-1)/m = 3/6 = 1/2 on every edge.
    G = nx.complete_graph(4)
    m = G.number_of_edges()

    result = min_norm_point(m, MinimumSpanningTree(G))

    assert all(v == Fraction(1, 2) for v in result.x)
    assert sum(e.weight for e in result.support) == 1


# ---------------------------------------------------------------------
# Support correctness
# ---------------------------------------------------------------------


def test_ground_truth_finds_exactly_two_forbidden_trees_on_house_graph():
    # Sanity check on the independent ground truth itself, matching the
    # claim validated in scratch/wolfe_min_norm.py: exactly 2 of the
    # house graph's 11 spanning trees are unusable.
    G, _ = demo.house_graph()
    forbidden = _ground_truth_forbidden_trees(G, Fraction(2, 3))
    assert len(forbidden) == 2


@pytest.mark.parametrize("min_norm_point", ALGORITHMS)
def test_house_graph_support_excludes_forbidden_trees(min_norm_point):
    G, _ = demo.house_graph()
    m = G.number_of_edges()
    forbidden = _ground_truth_forbidden_trees(G, Fraction(2, 3))

    result = min_norm_point(m, MinimumSpanningTree(G))

    used = {frozenset(frozenset(e) for e in entry.cons) for entry in result.support}
    assert used.isdisjoint(forbidden)


# ---------------------------------------------------------------------
# Away-step / eviction mechanism
# ---------------------------------------------------------------------


def test_wolfe_forced_forbidden_start_gets_evicted(capsys):
    G, _ = demo.house_graph()
    m = G.number_of_edges()
    idx = edge_index(G)
    forbidden = _ground_truth_forbidden_trees(G, Fraction(2, 3))
    forbidden_tree = tuple(tuple(e) for e in next(iter(forbidden)))

    n = _tree_vector(forbidden_tree, idx, m)
    result = min_norm_point_wolfe(
        m, MinimumSpanningTree(G), init_active_set=[(forbidden_tree, n)], verbose=True
    )

    assert result.extra_stats["active_set_removals"] >= 1
    assert all(v == Fraction(2, 3) for v in result.x)
    used = {frozenset(frozenset(e) for e in entry.cons) for entry in result.support}
    assert used.isdisjoint(forbidden)
    assert "evicted" in capsys.readouterr().out


# ---------------------------------------------------------------------
# Failure/reporting paths
# ---------------------------------------------------------------------


@pytest.mark.parametrize("min_norm_point", ALGORITHMS)
def test_verbose_prints_convergence_summary(min_norm_point, capsys):
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    min_norm_point(m, MinimumSpanningTree(G), verbose=True)

    assert "converged" in capsys.readouterr().out.lower()


def test_afw_raises_on_non_convergence():
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    with pytest.raises(RuntimeError, match="failed to converge"):
        min_norm_point_afw(m, MinimumSpanningTree(G), max_iter=0)


def test_wolfe_raises_on_non_convergence():
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    with pytest.raises(RuntimeError, match="failed to converge"):
        min_norm_point_wolfe(m, MinimumSpanningTree(G), max_major=0)


def test_wolfe_raises_on_minor_cycle_non_convergence():
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    with pytest.raises(RuntimeError, match="minor cycle failed to converge"):
        min_norm_point_wolfe(m, MinimumSpanningTree(G), max_minor=0)
