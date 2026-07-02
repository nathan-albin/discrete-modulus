"""
Operator functors on families.
"""

from collections.abc import Sequence

import numpy as np

from ..protocols import FloatArray, ShortestObjectFinder, ShortestResult


class UnionShortest:
    """
    Shortest object operator for a union of families.
    """

    def __init__(self, F: Sequence[ShortestObjectFinder]) -> None:
        self.F = F

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult:

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
    """

    def __init__(self, F: Sequence[ShortestObjectFinder]) -> None:
        self.F = F

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult:

        n = np.zeros(rho.shape)
        cons = []
        for f in self.F:
            result = f(rho, tol)
            assert result.n is not None
            cons.append(result.cons)
            n += result.n

        return ShortestResult(cons, n)
