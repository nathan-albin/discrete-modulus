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

ExactArray = NDArray[np.object_]
"""
A numpy object-dtype array, for exact-arithmetic alternatives to
`FloatArray`.

Not tied to any specific element type -- `dtype=object` erases it anyway,
so this covers an array of `fractions.Fraction` (the element type used
throughout this package, e.g. `min_norm_point`), but equally an array of
`mpmath.mpf`, a custom interval type, or anything else whose `+`/`*`/`<`
etc. numpy's elementwise dispatch can call. Anywhere a `FloatArray` is
accepted, an `ExactArray` may be used instead to get exact results end to
end (e.g. through `families.networkx_families`'s MST/shortest-path
lookups, which only rely on comparison and addition of edge weights).
"""


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
    n: FloatArray | ExactArray | None


class ShortestObjectFinder(Protocol):
    """
    Protocol for callables that find a "most violated constraint" for a
    given family, given the current density `rho`.
    """

    def __call__(self, rho: FloatArray | ExactArray, tol: float) -> ShortestResult:
        """
        Parameters
        ----------
        rho : numpy array
            The current density. An `ExactArray` may be passed instead of
            a `FloatArray` to get an exact result, if the implementation
            supports it (see `ExactArray`).

        tol : float
            The tolerance; may be ignored by implementations that don't
            need it (see `ShortestResult`'s `n` field for the "already
            admissible" case this exists to support).

        Returns
        -------
        ShortestResult
        """
        ...


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
    ) -> SubproblemResult:
        """
        Parameters
        ----------
        N : numpy array or scipy sparse matrix
            The usage matrix for the (sub)family being solved.

        p : float or np.inf
            The modulus energy exponent.

        sigma : numpy array, optional
            The weights sigma. If None, all weights are treated as 1.

        Returns
        -------
        SubproblemResult
        """
        ...


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
