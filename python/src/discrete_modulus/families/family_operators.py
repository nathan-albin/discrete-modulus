"""
Operator functors on families.
"""

from collections.abc import Callable, Sequence
from typing import Any

import numpy as np
from numpy.typing import NDArray

FloatArray = NDArray[np.float64]
ShortestFunc = Callable[[FloatArray, float], tuple[Any, FloatArray]]


class UnionShortest:
    """
    Shortest object operator for a union of families.
    """

    def __init__(self, F: Sequence[ShortestFunc]) -> None:
        self.F = F

    def __call__(self, rho: FloatArray, tol: float) -> tuple[Any, FloatArray]:

        results = [f(rho, tol) for f in self.F]
        lengths = [rho.dot(n) for cons, n in results]
        ind = np.argmin(lengths)
        return results[ind]


class SumShortest:
    """
    Shortest object operator for a summation of families.
    """

    def __init__(self, F: Sequence[ShortestFunc]) -> None:
        self.F = F

    def __call__(self, rho: FloatArray, tol: float) -> tuple[list[Any], FloatArray]:

        n = np.zeros(rho.shape)
        cons = []
        for f in self.F:
            c_f, n_f = f(rho, tol)
            cons.append(c_f)
            n += n_f

        return cons, n
