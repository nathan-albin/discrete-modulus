"""
Shared types and structural interfaces ("protocols") used across the
`discrete_modulus` package.

These formalize the two informal callback conventions the rest of the
package is built around:

- A "shortest object finder" (see `ShortestObjectFinder`), used by
  `algorithms.modulus` to grow the constraint set, and implemented by
  `families.networkx_families.ShortestConnectingPath`,
  `families.networkx_families.MinimumSpanningTree`,
  `families.family_operators.UnionShortest`, and
  `families.family_operators.SumShortest`.

- A "subproblem solver" (see `SubproblemSolver`), used by
  `algorithms.modulus` to re-optimize as constraints are added, and
  implemented by `algorithms.matrix_modulus`.

Anyone writing a new family or solver only needs to match these
`__call__` signatures; there is no base class to inherit from.
"""

from typing import Any, NamedTuple, Protocol

import numpy as np
import scipy.sparse as sp
from numpy.typing import NDArray

FloatArray = NDArray[np.float64]


class ShortestResult(NamedTuple):
    """
    The result of a `ShortestObjectFinder` call.

    Attributes
    ----------
    cons : object
        Any representation desired for describing the object found (e.g. a
        path, a set of edges). Purely informational; may be None.

    n : numpy array or None
        The row vector representing the corresponding constraint, to be
        added to the usage matrix. None if every constraint is already
        satisfied to within tolerance.
    """

    cons: Any
    n: FloatArray | None


class ShortestObjectFinder(Protocol):
    """
    Protocol for callables that find a "most violated constraint" for a
    given family, given the current density `rho`.
    """

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult: ...


class SubproblemResult(NamedTuple):
    """
    The result of a `SubproblemSolver` call.

    Attributes
    ----------
    mod : float
        Approximation to the modulus of the subproblem.

    rho : numpy array
        Approximation to an optimal density.

    lam : numpy array
        Approximation to the dual variables for the subproblem's
        constraints.
    """

    mod: float
    rho: FloatArray
    lam: FloatArray


class SubproblemSolver(Protocol):
    """
    Protocol for callables that solve a modulus subproblem given a usage
    matrix `N`.
    """

    def __call__(
        self,
        N: FloatArray | sp.spmatrix,
        p: float,
        sigma: FloatArray | None = None,
    ) -> SubproblemResult: ...


class ModulusResult(NamedTuple):
    """
    The result of running `algorithms.modulus`.

    Attributes
    ----------
    mod : float
        Approximation to modulus.

    cons : list
        List of constraints added during the iteration. The format of the
        elements of this list is determined by the `cons` field returned
        by the `find_shortest` callable.

    rho : numpy array
        Approximation to an optimal density.

    lam : numpy array
        Approximation to the dual variables for the constraints listed in
        `cons`.
    """

    mod: float
    cons: list[Any]
    rho: FloatArray
    lam: FloatArray
