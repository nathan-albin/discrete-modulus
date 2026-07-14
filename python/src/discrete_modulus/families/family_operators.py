"""
Operator functors on families.
"""

from collections.abc import Sequence

import numpy as np

from ..protocols import ExactArray, FloatArray, ShortestObjectFinder, ShortestResult


class UnionShortest:
    """
    Shortest object operator for a union of families.

    Given a collection of families (each represented by a
    `ShortestObjectFinder`), finds the single shortest object across all
    of them -- i.e. implements `ShortestObjectFinder` for
    Gamma_1 U Gamma_2 U ... U Gamma_k.
    """

    def __init__(self, F: Sequence[ShortestObjectFinder]) -> None:
        """
        Parameters
        ----------
        F : sequence of ShortestObjectFinder
            The finders for the families being unioned.
        """
        self.F = F

    def __call__(self, rho: FloatArray | ExactArray, tol: float) -> ShortestResult:
        """
        Finds the shortest object across all families in the union.

        Parameters
        ----------
        rho : numpy array
            The current density.

        tol : float
            Passed through to each finder in `F`; otherwise unused here.

        Returns
        -------
        ShortestResult
            The result from whichever finder in `F` produced the object
            of smallest rho-length.
        """

        results = [f(rho, tol) for f in self.F]
        lengths = []
        for result in results:
            assert result.n is not None
            lengths.append(rho.dot(result.n))
        ind = np.argmin(lengths)
        return results[ind]


class SumShortest:
    """
    Shortest object operator for a summation of families.

    Given a collection of families, finds the "sum" object obtained by
    combining the shortest object from each family -- i.e. implements
    `ShortestObjectFinder` for Gamma_1 + Gamma_2 + ... + Gamma_k.
    """

    def __init__(self, F: Sequence[ShortestObjectFinder]) -> None:
        """
        Parameters
        ----------
        F : sequence of ShortestObjectFinder
            The finders for the families being summed.
        """
        self.F = F

    def __call__(self, rho: FloatArray | ExactArray, tol: float) -> ShortestResult:
        """
        Combines the shortest object from each family in the sum.

        Parameters
        ----------
        rho : numpy array
            The current density.

        tol : float
            Passed through to each finder in `F`; otherwise unused here.

        Returns
        -------
        ShortestResult
            `cons` is the list of each family's individual result (in
            the order of `F`); `n` is the elementwise sum of their usage
            vectors, with the same dtype as `rho`.
        """

        # mypy can't infer, from a union-typed rho, that dtype=rho.dtype
        # produces a same-union-member array.
        n: FloatArray | ExactArray = np.zeros(rho.shape, dtype=rho.dtype)  # type: ignore[assignment]
        cons = []
        for f in self.F:
            result = f(rho, tol)
            assert result.n is not None
            cons.append(result.cons)
            n = n + result.n

        return ShortestResult(cons, n)
