from __future__ import annotations

from collections.abc import Callable
from time import perf_counter
from warnings import warn

import cvxpy as cvx
import numpy as np
import scipy.sparse as sp
from numpy.typing import NDArray

FloatArray = NDArray[np.float64]


def matrix_modulus(
    N: FloatArray | sp.spmatrix,
    p: float = 2,
    sigma: FloatArray | None = None,
) -> tuple[float, FloatArray, FloatArray]:
    """
    Computes the modulus of a family given its N matrix.

    Parameters
    ----------
    N : numpy array OR scipy sparse matrix
        The N matrix for the family.

    p : float or np.inf
        The modulus energy exponent.

    sigma : numpy array
        The weights sigma.  If sigma = None, all weights
        are treated as 1.

    Returns
    -------
    mod : float
        An approximation of the modulus.

    rho : numpy array
        An optimal rho^* for modulus.

    lam : numpy array
        An optimal dual lambda^* for modulus.

    Notes
    -----
    This function is just a template solver.  For specialized
    problems, it is probably best to implement a particular
    solver based on the energy exponent and the desired
    tolerances in the approximation.
    """

    # problem dimension
    m = N.shape[1]

    # set sigma to default if necessary
    if sigma is None:
        sigma = np.ones(m)

    # convert inputs to cvxpy constants
    N_const = cvx.Constant(N)
    sigma_const = cvx.Constant(sigma)

    # primal variables
    rho = cvx.Variable(m)

    # objective
    if p != np.inf:
        obj = cvx.Minimize(sigma_const.T @ rho**p)
    else:
        obj = cvx.Minimize(cvx.max(cvx.multiply(sigma_const, rho)))

    # constraints
    cons = [rho >= 0, N_const @ rho >= 1]

    # set up the problem
    prob = cvx.Problem(obj, cons)

    # attempt to solve
    prob.solve()
    if prob.status != "optimal":
        warn(f"cvxpy solve returned status {prob.status}", stacklevel=2)

    return prob.value, np.array(rho.value).flatten(), np.array(cons[1].dual_value).flatten()


SolveSubproblem = Callable[[sp.spmatrix, float, FloatArray], tuple[float, FloatArray, FloatArray]]
FindShortest = Callable[[FloatArray, float], tuple[object, FloatArray | None]]


def modulus(
    m: int,
    solve_subproblem: SolveSubproblem,
    find_shortest: FindShortest,
    p: float = 2,
    sigma: FloatArray | None = None,
    tol: float = 1e-3,
    max_iter: int = 1000,
    output_every: int | None = None,
) -> tuple[float, list, FloatArray, FloatArray]:
    """
    Implements the basic algorithm for modulus.

    Parameters
    ----------
    m : int
        The dimension of the modulus problem (number of edges).

    solve_subproblem : callable
        See below.

    find_shortest : callable
        See below.

    p : float or np.inf
        The modulus energy exponent.

    sigma : numpy array
        The weights sigma.  If sigma = None, all weights
        are treated as 1.

    tol : float
        The tolerance.  The modulus algorithm stops when the approximate
        density is within tol of being admissible.

    max_iter : int
        Maximum number of iterations to perform before terminating with an error.

    output_every : int
        Frequency of output to stderr.  If this is set to None, output is supressed.

    Returns
    -------
    mod : float
        Approximation to modulus.

    cons : list
        List of constraints added during the iteration.  The format of the elements of
        this list is determined by the output of the find_violated_constraint function.

    rho : numpy array
        Approximation to an optimal density.

    lam : numpy array
        Approximation to the dual variables for the constraints listed in cons.

    Raises
    ------
    RuntimeError
        If the algorithm fails to converge to within `tol` after `max_iter`
        iterations.

    Notes
    -----
    The function solve_subproblem should have the following signature

        mod, rho, lam = solve_subproblem(N, p, sigma)

    See the function matrix_modulus for an example.

    The function find_shortest should have the following signature

        cons, n = find_shortest(rho, tol)

    This function should find a "most violated constraint" using the specified values
    for rho.  Upon return, cons may contain any representation desired for describing
    the constraint.  (This is purely informational for the user and it is acceptable
    for cons to be set to None.)  n should contain the numpy row vector representing the
    violated constraint.  This is the row that will be added to N on the next iteration.

    The argument tol may be ignored.  However, it is acceptable for the function to return
    the tuple (None, None) if every constraint is satisfied to within a tolerance of tol.
    """

    # timers
    search_time = 0.0
    update_time = 0.0
    mod_start = perf_counter()

    # initialize variables
    rho = np.zeros(m)
    N = sp.csr_matrix((0, m))
    lam = np.array([])
    mod = 0.0
    upper: float | FloatArray = np.inf
    cons: list[object] = []

    # default sigma
    if sigma is None:
        sigma = np.ones(m)

    # initialize output table
    if output_every:
        print(
            "| {:>6s} | {:>9s} | {:>9s} | {:>9s} | {:>6s} | {:>9s} |".format(
                "it", "l bnd", "u bnd", "rel gap", "# cons", "time (s)"
            )
        )
        print("+--------+-----------+-----------+-----------+--------+-----------+")

    # loop to at most max_iter
    for iter_count in range(max_iter):
        # find a constraint to add
        start = perf_counter()
        c, n = find_shortest(rho, tol)
        search_time += perf_counter() - start

        # compute the length of the shortest object
        if n is None:
            length = 1.0
        else:
            length = n.dot(rho)

        # update the upper bound
        if length > 0:
            if p == np.inf:
                upper = np.abs(sigma * rho / length)
            else:
                upper = np.sum(sigma * (rho / length) ** p)

        # check if we can stop
        if length > 1 - tol:
            if output_every:
                rel_gap = (upper - mod) / mod
                elapsed = perf_counter() - mod_start
                print(
                    f"| {iter_count + 1:6d} | {mod:9.3e} | {upper:9.3e} | {rel_gap:9.3e} "
                    f"| {N.shape[0]:6d} | {elapsed:9.3e} |"
                )

                print()
                print(f"program running time = {perf_counter() - mod_start} sec")
                print(f"constraint search    = {search_time} sec")
                print(f"solution update      = {update_time} sec")

            return mod, cons, rho, lam

        # if not, we need to add a constraint
        assert n is not None
        # scipy-stubs doesn't model vstack's runtime support for mixing
        # sparse and dense blocks; this call is valid at runtime.
        N = sp.vstack([N, n], format="csr")  # type: ignore[call-overload]
        cons.append(c)

        # re-optimize
        start = perf_counter()
        mod, rho, lam = solve_subproblem(N, p, sigma)
        update_time += perf_counter() - start

        # print some feedback if desired
        if output_every and (iter_count + 1) % output_every == 0:
            if mod == 0:
                rel_gap = np.inf
            else:
                rel_gap = (upper - mod) / mod
            elapsed = perf_counter() - mod_start
            print(
                f"| {iter_count + 1:6d} | {mod:.3e} | {upper:.3e} | {rel_gap:.3e} "
                f"| {N.shape[0]:6d} | {elapsed:.3e} |"
            )

    # if we got here, we failed to converge
    raise RuntimeError(f"Modulus algorithm failed to converge in {max_iter} iterations.")
