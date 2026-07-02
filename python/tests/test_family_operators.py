"""
Tests for discrete_modulus.families.family_operators.

These use a simple fake finder functor with a pre-baked result, so they
exercise pure combinator logic (picking a minimum / summing) without
depending on any real graph or modulus computation.
"""

from __future__ import annotations

import numpy as np

from discrete_modulus.families.family_operators import SumShortest, UnionShortest
from discrete_modulus.protocols import FloatArray, ShortestResult


class FakeFinder:
    """A ShortestObjectFinder that ignores rho/tol and always returns the
    same pre-baked result."""

    def __init__(self, cons: object, n: FloatArray) -> None:
        self._result = ShortestResult(cons, np.asarray(n, dtype=float))

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult:
        return self._result


def test_union_shortest_picks_minimum_length():
    rho = np.array([1.0, 1.0, 1.0])
    short = FakeFinder("short", [1, 0, 0])  # length = rho . n = 1
    long_ = FakeFinder("long", [1, 1, 1])  # length = 3
    union = UnionShortest([long_, short])

    result = union(rho, 1e-3)

    assert result.cons == "short"
    assert np.array_equal(result.n, [1, 0, 0])


def test_union_shortest_with_single_finder():
    rho = np.array([1.0, 1.0])
    only = FakeFinder("only", [1, 1])
    union = UnionShortest([only])

    result = union(rho, 1e-3)

    assert result.cons == "only"


def test_sum_shortest_adds_vectors_and_collects_cons():
    rho = np.array([1.0, 1.0, 1.0])
    a = FakeFinder("a", [1, 0, 0])
    b = FakeFinder("b", [0, 1, 0])
    total = SumShortest([a, b])

    result = total(rho, 1e-3)

    assert result.cons == ["a", "b"]
    assert np.array_equal(result.n, [1, 1, 0])


def test_sum_shortest_with_empty_family_gives_zero_vector():
    rho = np.array([1.0, 1.0])
    total = SumShortest([])

    result = total(rho, 1e-3)

    assert result.cons == []
    assert np.array_equal(result.n, [0, 0])
