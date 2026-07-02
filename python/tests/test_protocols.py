"""
Sanity tests for the shared NamedTuple/Protocol types in
discrete_modulus.protocols: unpacking and attribute access should both
work, and the "purely informational, may be None" fields should allow
None.
"""

import numpy as np

from discrete_modulus.protocols import ModulusResult, ShortestResult, SubproblemResult


def test_shortest_result_unpacks_and_has_attrs():
    n = np.array([1.0, 0.0])
    result = ShortestResult(cons=["a", "b"], n=n)

    cons, n_out = result

    assert cons == ["a", "b"]
    assert np.array_equal(n_out, n)
    assert result.cons == ["a", "b"]
    assert np.array_equal(result.n, n)


def test_shortest_result_allows_none_fields():
    result = ShortestResult(cons=None, n=None)
    assert result.cons is None
    assert result.n is None


def test_subproblem_result_unpacks_and_has_attrs():
    rho = np.array([0.5, 0.5])
    lam = np.array([1.0])
    result = SubproblemResult(mod=0.5, rho=rho, lam=lam)

    mod, rho_out, lam_out = result

    assert mod == 0.5
    assert np.array_equal(rho_out, rho)
    assert result.lam is lam


def test_modulus_result_unpacks_and_has_attrs():
    rho = np.array([0.5, 0.5])
    lam = np.array([1.0])
    result = ModulusResult(mod=0.5, cons=["a"], rho=rho, lam=lam)

    mod, cons, rho_out, lam_out = result

    assert mod == 0.5
    assert cons == ["a"]
    assert result.rho is rho
    assert result.lam is lam
