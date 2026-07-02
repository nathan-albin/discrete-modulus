"""
Tests for discrete_modulus.algorithms: matrix_modulus and modulus.

Test strategy
-------------
1. Analytic cases with closed-form values, derived from standard modulus
   theory and confirmed numerically against this implementation before
   being written down here:
   - p=2 modulus of connecting paths equals the effective conductance of
     the associated unit-resistor network (series adds resistances,
     parallel adds conductances).
   - p=1 modulus of connecting paths equals the minimum edge cut
     (LP duality with max-flow/min-cut).
   - p=inf modulus of connecting paths equals 1 / (shortest-path distance).

2. Cross-checks between the brute-force LP (`matrix_modulus` on the fully
   enumerated family) and the incremental algorithm (`modulus` with the
   corresponding functor). These must always agree, regardless of whether
   a closed form is known, so this is the main correctness engine and
   generalizes to any graph/family/p.
"""

from __future__ import annotations

import networkx as nx
import numpy as np
import pytest
from helpers import edge_index, full_usage_matrix, path_edges

from discrete_modulus import demo
from discrete_modulus.algorithms import matrix_modulus, modulus
from discrete_modulus.families.networkx_families import (
    MinimumSpanningTree,
    ShortestConnectingPath,
)
from discrete_modulus.protocols import ShortestResult

# ---------------------------------------------------------------------
# modulus: the (None, None) "already admissible" signal
# ---------------------------------------------------------------------


def test_modulus_stops_immediately_on_none_signal():
    # Per the find_shortest contract, returning ShortestResult(None, None)
    # signals that every constraint is already satisfied.
    def already_admissible(rho, tol):
        return ShortestResult(None, None)

    result = modulus(3, matrix_modulus, already_admissible, p=2, tol=1e-3, max_iter=10)

    assert result.mod == 0.0
    assert result.cons == []


# ---------------------------------------------------------------------
# matrix_modulus: analytic cases
# ---------------------------------------------------------------------


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_series_path_modulus_p2(n):
    N = np.ones((1, n))
    assert matrix_modulus(N, p=2).mod == pytest.approx(1 / n)


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_series_path_modulus_p1(n):
    N = np.ones((1, n))
    assert matrix_modulus(N, p=1).mod == pytest.approx(1.0)


@pytest.mark.parametrize("n", [1, 2, 3, 4, 5])
def test_series_path_modulus_pinf(n):
    N = np.ones((1, n))
    assert matrix_modulus(N, p=np.inf).mod == pytest.approx(1 / n)


@pytest.mark.parametrize("n1,n2", [(1, 1), (2, 3), (1, 4), (3, 3)])
def test_parallel_paths_modulus_p2_adds_conductances(n1, n2):
    m = n1 + n2
    N = np.zeros((2, m))
    N[0, :n1] = 1
    N[1, n1:] = 1
    assert matrix_modulus(N, p=2).mod == pytest.approx(1 / n1 + 1 / n2)


@pytest.mark.parametrize("n1,n2", [(1, 1), (2, 3), (1, 4), (3, 3)])
def test_parallel_paths_modulus_p1_is_min_cut(n1, n2):
    m = n1 + n2
    N = np.zeros((2, m))
    N[0, :n1] = 1
    N[1, n1:] = 1
    assert matrix_modulus(N, p=1).mod == pytest.approx(2.0)


def test_house_graph_connecting_paths_modulus_pinf_is_inverse_distance():
    G, _ = demo.house_graph()
    idx = edge_index(G)
    paths = [path_edges(p) for p in nx.all_simple_paths(G, 0, 3)]
    N = full_usage_matrix(paths, idx, G.number_of_edges())

    d = nx.shortest_path_length(G, 0, 3)
    assert matrix_modulus(N, p=np.inf).mod == pytest.approx(1 / d)


def test_house_graph_connecting_paths_modulus_p1_is_min_cut():
    G, _ = demo.house_graph()
    idx = edge_index(G)
    paths = [path_edges(p) for p in nx.all_simple_paths(G, 0, 3)]
    N = full_usage_matrix(paths, idx, G.number_of_edges())

    min_cut_size = len(nx.minimum_edge_cut(G, 0, 3))
    assert matrix_modulus(N, p=1).mod == pytest.approx(min_cut_size)


def test_matrix_modulus_result_is_nonnegative():
    # regression: solver noise used to leave tiny negative entries in rho/lam
    N = np.ones((1, 3))
    result = matrix_modulus(N, p=1)
    assert (result.rho >= 0).all()
    assert (result.lam >= 0).all()


def test_matrix_modulus_monotonic_in_family_size():
    # Adding an object to a family can only increase (or keep equal) the
    # modulus: more constraints -> smaller admissible set -> larger min.
    N_small = np.ones((1, 4))
    N_big = np.vstack([N_small, [1, 1, 0, 0]])
    assert matrix_modulus(N_big, p=2).mod >= matrix_modulus(N_small, p=2).mod - 1e-9


# ---------------------------------------------------------------------
# modulus: cross-checks against brute-force matrix_modulus
# ---------------------------------------------------------------------


@pytest.mark.parametrize("p", [1.0, 2.0, 3.0, np.inf])
def test_modulus_matches_brute_force_spanning_trees(p):
    G, _ = demo.house_graph()
    idx = edge_index(G)
    m = G.number_of_edges()
    N = full_usage_matrix(list(demo.spanning_trees(G)), idx, m)

    brute = matrix_modulus(N, p=p)
    incremental = modulus(m, matrix_modulus, MinimumSpanningTree(G), p=p, tol=1e-7, max_iter=500)

    assert incremental.mod == pytest.approx(brute.mod, rel=1e-4, abs=1e-6)


@pytest.mark.parametrize("p", [1.0, 2.0, 3.0, np.inf])
def test_modulus_matches_brute_force_connecting_paths(p):
    G, _ = demo.house_graph()
    idx = edge_index(G)
    m = G.number_of_edges()
    paths = [path_edges(path) for path in nx.all_simple_paths(G, 0, 3)]
    N = full_usage_matrix(paths, idx, m)

    brute = matrix_modulus(N, p=p)
    incremental = modulus(
        m, matrix_modulus, ShortestConnectingPath(G, [0], [3]), p=p, tol=1e-7, max_iter=500
    )

    assert incremental.mod == pytest.approx(brute.mod, rel=1e-4, abs=1e-6)


# ---------------------------------------------------------------------
# modulus: control flow
# ---------------------------------------------------------------------


def test_modulus_raises_on_non_convergence():
    G, _ = demo.house_graph()
    m = G.number_of_edges()
    with pytest.raises(RuntimeError):
        modulus(m, matrix_modulus, MinimumSpanningTree(G), p=2, tol=1e-12, max_iter=1)


def test_modulus_result_shape():
    G, _ = demo.house_graph()
    m = G.number_of_edges()
    result = modulus(m, matrix_modulus, MinimumSpanningTree(G), p=2, tol=1e-6, max_iter=200)

    assert result.mod == pytest.approx(0.375)
    assert isinstance(result.cons, list)
    assert len(result.rho) == m


def test_modulus_output_every_prints_progress_without_error(capsys):
    G, _ = demo.house_graph()
    m = G.number_of_edges()

    result = modulus(
        m, matrix_modulus, MinimumSpanningTree(G), p=2, tol=1e-6, max_iter=200, output_every=1
    )

    out = capsys.readouterr().out
    assert result.mod == pytest.approx(0.375)
    assert "it" in out and "l bnd" in out and "u bnd" in out  # table header
    assert "program running time" in out  # final summary block
