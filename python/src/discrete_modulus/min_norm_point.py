"""
Away-step Frank-Wolfe and Wolfe's (1976) minimum-norm-point algorithm:
two ways to find a sparse pmf on a family Gamma (e.g. spanning trees) whose
expected usage vector is a prescribed point eta in conv(Gamma) -- the
"medium gap" pmf-construction step described in
`scratch/Certification_Plan.md` Phase 0.

Both algorithms minimize f(x) = ||x||^2 over conv(Gamma), given only a
linear-minimization oracle (`ShortestObjectFinder`, the same protocol
`algorithms.modulus` uses -- for spanning trees,
`families.networkx_families.MinimumSpanningTree`). The minimizer eta* is
`conv(Gamma)`'s minimum-norm point; the active-set weights at convergence
are exactly the desired pmf, by Caratheodory sparse (support size at most
dim(conv(Gamma)) + 1).

Vanilla (fixed-step) Frank-Wolfe on this objective is the "Plus-1
algorithm": w_{k+1} = w_k + 1_{argmin oracle(w_k)}. It's provably only
O(1/k) and zig-zags badly whenever the minimizer lies on a low-dimensional
face of the polytope (Guelat & Marcotte 1986) -- exactly the case here,
since eta* is highly degenerate. Both algorithms below fix this by
tracking an *active set* of visited vertices and explicitly removing
("away step" / "eviction") a vertex whose weight would otherwise go
negative:

- `min_norm_point_afw`: classic away-step Frank-Wolfe (Guelat & Marcotte
  1986; Lacoste-Julien & Jaggi 2015). Each iteration takes either a
  forward step (towards the oracle's vertex) or an away step (away from
  the worst vertex currently in the active set), whichever the closed-form
  line search predicts more decrease from. O(active-set size) per
  iteration. Kept for comparison, but not recommended downstream -- see
  its own docstring's "Notes" for why.

- `min_norm_point_wolfe`: Wolfe's (1976) full minimum-norm-point
  algorithm (also the basis of Fujishige's min-norm-point method for
  submodular function minimization -- matroid rank functions, e.g. the
  graphic matroid here, are submodular). Each major iteration projects
  onto the affine hull of the active set (a "minor cycle" of exact linear
  solves), evicting any vertex whose affine coefficient goes negative,
  until every active weight is positive. O(r^3) per minor cycle, r =
  active-set size.

Everything is exact `fractions.Fraction` arithmetic (via `ExactArray`,
a `dtype=object` numpy array of `Fraction`) -- no floating-point
tolerances anywhere, matching `spanning_tree_modulus`'s exactness ethos.
This is validated as reasonable by `scratch/wolfe_min_norm_exact.py`: the
minor cycle only ever solves a small (r+1)x(r+1) linear system, cheap
enough to do exactly.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction
from typing import Any, NamedTuple

import numpy as np

from .protocols import ExactArray, FloatArray, ShortestObjectFinder

ActiveKey = tuple[Any, ...]


class SupportEntry(NamedTuple):
    """
    One vertex of the pmf's support.

    Attributes
    ----------
    cons : object
        Whatever `ShortestObjectFinder.cons` returned for this vertex
        (e.g. a spanning tree's edge list).

    n : ExactArray
        The vertex's exact usage vector.

    weight : Fraction
        Its weight in the pmf.
    """

    cons: Any
    n: ExactArray
    weight: Fraction


class MinNormPointResult(NamedTuple):
    """
    The result of `min_norm_point_afw` or `min_norm_point_wolfe`.

    Attributes
    ----------
    x : ExactArray
        The minimum-norm point of conv(Gamma) (eta* for this round).

    support : list of SupportEntry
        The sparse pmf: `sum(e.weight * e.n for e in support) == x`,
        `sum(e.weight for e in support) == 1`.

    iterations : int
        Number of update steps taken (major iterations for Wolfe's
        algorithm, forward/away steps for AFW) before convergence.

    oracle_calls : int
        Number of calls to `find_shortest` -- the fair cost unit for
        comparing the two algorithms, since their per-iteration cost
        otherwise differs (O(r) for AFW vs. O(r^3) for Wolfe's algorithm).

    extra_stats : dict of str to int
        Algorithm-specific counters. Both algorithms set
        `"active_set_removals"` (AFW's drop steps / Wolfe's evictions --
        the same event, a vertex's weight being driven to exactly zero
        and removed, under different classical names). Wolfe's algorithm
        additionally sets `"minor_iterations"`.
    """

    x: ExactArray
    support: list[SupportEntry]
    iterations: int
    oracle_calls: int
    extra_stats: dict[str, int]


def _zero_vector(m: int) -> ExactArray:
    return np.array([Fraction(0)] * m, dtype=object)


def _key(n: ExactArray) -> ActiveKey:
    return tuple(n.tolist())


def _as_rational(n: FloatArray | ExactArray) -> ExactArray:
    """
    Casts a usage vector to a genuinely `Fraction`-valued array.

    `ShortestObjectFinder` implementations aren't required to fill a
    `dtype=object` result with `Fraction` specifically -- e.g.
    `MinimumSpanningTree` writes plain `0`/`1`. Left alone, a Gram matrix
    built directly from such a vector (as Wolfe's algorithm's first minor
    cycle does) is `int`-valued, and Python's `int / int` is float
    division -- silently contaminating all downstream arithmetic with
    float noise despite the `dtype=object` array still *looking* exact.
    Normalizing at the oracle boundary makes every vector provably
    `Fraction`-valued before any arithmetic sees it, rather than relying
    on incidental promotion via whichever other operand happens to be a
    `Fraction` first.
    """
    return np.array([Fraction(v) for v in n], dtype=object)


def _call_oracle(find_shortest: ShortestObjectFinder, x: ExactArray) -> tuple[Any, ExactArray]:
    result = find_shortest(x, 0.0)
    assert result.n is not None
    return result.cons, _as_rational(result.n)


def _weighted_sum(active: dict[ActiveKey, SupportEntry], m: int) -> ExactArray:
    x = _zero_vector(m)
    for entry in active.values():
        x = x + entry.weight * entry.n
    return x


def _seed_active_set(
    init_active_set: Sequence[tuple[Any, ExactArray]] | None,
    find_shortest: ShortestObjectFinder,
    m: int,
) -> tuple[dict[ActiveKey, SupportEntry], ExactArray, int]:
    """
    Builds the initial active set (equal weights) and the point it
    represents.

    Returns
    -------
    active : dict
        The initial active set, keyed by `_key`.

    x : ExactArray
        The point the active set represents.

    oracle_calls : int
        1 if a cold-start oracle call was made (`init_active_set is
        None`), else 0.
    """

    if init_active_set is None:
        cold_start = _call_oracle(find_shortest, _zero_vector(m))
        entries: Sequence[tuple[Any, ExactArray]] = [cold_start]
        oracle_calls = 1
    else:
        entries = [(cons, _as_rational(n)) for cons, n in init_active_set]
        oracle_calls = 0

    weight = Fraction(1, len(entries))
    active = {_key(n): SupportEntry(cons, n, weight) for cons, n in entries}

    return active, _weighted_sum(active, m), oracle_calls


def _apply_step(
    active: dict[ActiveKey, SupportEntry],
    scale: Fraction,
    adjust_key: ActiveKey,
    adjust_cons: Any,
    adjust_n: ExactArray,
    weight_delta: Fraction,
) -> dict[ActiveKey, SupportEntry]:
    """
    Rescales every active-set weight by `scale`, then adds `weight_delta`
    to the entry at `adjust_key` (inserting a new entry if it's not
    already active). Drops any entry whose resulting weight is exactly
    zero.

    Notes
    -----
    Forward and away steps are both affine updates of this same shape --
    `x_new = scale*x + weight_delta*adjust_n` at the level of barycentric
    coordinates -- with opposite-signed `scale`/`weight_delta` (see
    `min_norm_point_afw`).
    """

    new_active: dict[ActiveKey, SupportEntry] = {}
    for k, entry in active.items():
        w = entry.weight * scale
        if k == adjust_key:
            w += weight_delta
        if w != 0:
            new_active[k] = SupportEntry(entry.cons, entry.n, w)

    if adjust_key not in active and adjust_key not in new_active and weight_delta != 0:
        new_active[adjust_key] = SupportEntry(adjust_cons, adjust_n, weight_delta)

    return new_active


def min_norm_point_afw(
    m: int,
    find_shortest: ShortestObjectFinder,
    init_active_set: Sequence[tuple[Any, ExactArray]] | None = None,
    max_iter: int = 10_000,
    verbose: bool = False,
) -> MinNormPointResult:
    """
    Finds the minimum-norm point of conv(Gamma) via away-step Frank-Wolfe.

    Parameters
    ----------
    m : int
        The dimension of the problem (number of edges).

    find_shortest : ShortestObjectFinder
        The forward-direction (linear-minimization) oracle for Gamma. See
        `discrete_modulus.protocols`; e.g.
        `families.networkx_families.MinimumSpanningTree(G)` for spanning
        trees. Called as `find_shortest(x, 0.0)`; `tol` is unused since
        convergence is checked exactly.

    init_active_set : sequence of (cons, ExactArray), optional
        If given, seeds the active set with these vertices at equal
        weight, instead of the default cold start (one oracle call on the
        zero vector). Useful for forcing a specific (e.g. known-bad)
        starting vertex, to test the away-step/drop-step mechanism
        directly.

    max_iter : int
        Maximum number of forward/away steps before giving up.

    verbose : bool
        If True, prints a convergence summary and each active-set removal
        to stdout.

    Returns
    -------
    MinNormPointResult

    Raises
    ------
    RuntimeError
        If the algorithm fails to converge within `max_iter` iterations.

    Notes
    -----
    **Not recommended for downstream use -- kept for comparison, but
    `min_norm_point_wolfe` is the one to call.** Unlike Wolfe's algorithm,
    AFW has no guaranteed bound on exact-arithmetic denominator growth:
    each step's line-search `gamma` is a "generic" rational number, and
    rescaling every active weight by `(1 +/- gamma)` every iteration
    compounds denominators multiplicatively with no reduction, rather than
    re-deriving them from a small integer system each time (Wolfe's minor
    cycle does exactly that, which is why its denominators stay bounded in
    practice -- see `scratch/Certification_Plan.md` for the theory).

    This isn't a theoretical worry -- it was confirmed, while implementing
    this module, to actually happen every time the away-step branch (the
    one at line-search choice `decrease_away > decrease_fw` below)
    actually triggers, via three independent attempts to find a cheap
    counter-example: (1) seeding with a single known-forbidden tree blew
    up to 50+ digit numerators/denominators within about 7 iterations with
    no sign of stopping; (2) an isomorphic relabeling of `demo.house_graph`
    (different networkx MST tie-breaking) hit the same blowup on a *cold*
    start once it ran past ~7 iterations; (3) a systematic sweep of 19
    hand-picked good-tree/bad-tree initial weight ratios never found one
    where the away branch triggered without the run already being deep
    enough to be blowing up. Cold starts that converge in a handful of
    iterations (`demo.house_graph()`, `nx.complete_graph(4)`) never reach
    the away branch at all and stay cheap and exact -- which is also why
    this function's own test coverage stops there; see
    `test_min_norm_point.py`'s module docstring.
    """

    active, x, oracle_calls = _seed_active_set(init_active_set, find_shortest, m)
    active_set_removals = 0

    for iteration in range(max_iter):
        s_cons, s_n = _call_oracle(find_shortest, x)
        oracle_calls += 1
        s_key = _key(s_n)

        xx = x.dot(x)
        xs = x.dot(s_n)
        if xs >= xx:
            if verbose:
                print(
                    f"AFW converged after {iteration} iterations, "
                    f"{oracle_calls} oracle calls, {active_set_removals} removals"
                )
            return MinNormPointResult(
                x=x,
                support=list(active.values()),
                iterations=iteration,
                oracle_calls=oracle_calls,
                extra_stats={"active_set_removals": active_set_removals},
            )

        away_key = max(active, key=lambda k: x.dot(active[k].n))
        away_entry = active[away_key]

        # Not converged, so decrease_fw = xx - xs > 0 strictly; and the
        # away branch is only taken when decrease_away > decrease_fw > 0,
        # so both directions' step-length denominators below are provably
        # nonzero and gamma is provably positive -- no clipping to 0 or
        # zero-division guards needed.
        decrease_fw = xx - xs
        decrease_away = x.dot(away_entry.n) - xx

        old_active = active
        if decrease_fw >= decrease_away:
            d = s_n - x
            gamma = min(decrease_fw / d.dot(d), Fraction(1))
            active = _apply_step(active, 1 - gamma, s_key, s_cons, s_n, gamma)
        else:  # pragma: no cover -- see this function's docstring "Notes"
            d = x - away_entry.n
            gamma_max = away_entry.weight / (1 - away_entry.weight)
            gamma = min(decrease_away / d.dot(d), gamma_max)
            active = _apply_step(active, 1 + gamma, away_key, away_entry.cons, away_entry.n, -gamma)

        removed = old_active.keys() - active.keys()
        if verbose:
            for k in removed:
                print(f"  removed: {old_active[k].cons}")
        active_set_removals += len(removed)

        x = _weighted_sum(active, m)

    raise RuntimeError(f"AFW algorithm failed to converge in {max_iter} iterations.")


def _solve_exact(A: list[list[Fraction]], b: list[Fraction]) -> list[Fraction]:
    """Exact Gaussian elimination with partial pivoting. Solves Ax = b."""

    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        pivot = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[pivot] = M[pivot], M[col]
        pv = M[col][col]
        M[col] = [v / pv for v in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                factor = M[r][col]
                M[r] = [M[r][k] - factor * M[col][k] for k in range(n + 1)]
    return [M[r][n] for r in range(n)]


def _solve_affine_hull(gram: list[list[Fraction]]) -> list[Fraction]:
    """
    Finds the affine coefficients mu (summing to 1) minimizing
    `||sum_i mu_i v_i||^2`, given the active set's Gram matrix, via the
    KKT system

        [Gram  1] [mu]   [0]
        [1^T   0] [nu] = [1]

    (nu is the Lagrange multiplier for the sum-to-one constraint,
    discarded).
    """

    r = len(gram)
    A = [[gram[i][j] for j in range(r)] + [Fraction(1)] for i in range(r)]
    A.append([Fraction(1)] * r + [Fraction(0)])
    b = [Fraction(0)] * r + [Fraction(1)]
    return _solve_exact(A, b)[:r]


def min_norm_point_wolfe(
    m: int,
    find_shortest: ShortestObjectFinder,
    init_active_set: Sequence[tuple[Any, ExactArray]] | None = None,
    max_major: int = 200,
    max_minor: int = 200,
    verbose: bool = False,
) -> MinNormPointResult:
    """
    Finds the minimum-norm point of conv(Gamma) via Wolfe's (1976)
    minimum-norm-point algorithm.

    Parameters
    ----------
    m : int
        The dimension of the problem (number of edges).

    find_shortest : ShortestObjectFinder
        The forward-direction (linear-minimization) oracle for Gamma. See
        `min_norm_point_afw`.

    init_active_set : sequence of (cons, ExactArray), optional
        See `min_norm_point_afw`.

    max_major : int
        Maximum number of major iterations before giving up.

    max_minor : int
        Maximum number of minor-cycle (affine-projection) iterations
        within a single major iteration before giving up.

    verbose : bool
        If True, prints a convergence summary and each eviction to
        stdout.

    Returns
    -------
    MinNormPointResult

    Raises
    ------
    RuntimeError
        If the algorithm fails to converge within `max_major` major
        iterations, or a minor cycle fails to converge within `max_minor`
        iterations.
    """

    active, x, oracle_calls = _seed_active_set(init_active_set, find_shortest, m)
    active_set_removals = 0
    minor_iterations = 0

    for major in range(max_major):
        s_cons, s_n = _call_oracle(find_shortest, x)
        oracle_calls += 1
        s_key = _key(s_n)

        if x.dot(s_n) >= x.dot(x):
            if verbose:
                print(
                    f"Wolfe's algorithm converged after {major} major, "
                    f"{minor_iterations} minor iterations, {active_set_removals} evictions"
                )
            return MinNormPointResult(
                x=x,
                support=list(active.values()),
                iterations=major,
                oracle_calls=oracle_calls,
                extra_stats={
                    "active_set_removals": active_set_removals,
                    "minor_iterations": minor_iterations,
                },
            )

        if s_key not in active:
            active[s_key] = SupportEntry(s_cons, s_n, Fraction(0))

        for _minor in range(1, max_minor + 1):
            minor_iterations += 1
            keys = list(active.keys())
            vecs = [active[k].n for k in keys]
            gram = [[vecs[i].dot(vecs[j]) for j in range(len(keys))] for i in range(len(keys))]
            mu = _solve_affine_hull(gram)

            if all(w > 0 for w in mu):
                for k, w in zip(keys, mu, strict=True):
                    active[k] = active[k]._replace(weight=w)
                break

            lam = [active[k].weight for k in keys]
            theta = Fraction(1)
            for lam_i, mu_i in zip(lam, mu, strict=True):
                if mu_i < lam_i:
                    theta = min(theta, lam_i / (lam_i - mu_i))
            new_lam = [lam_i + theta * (mu_i - lam_i) for lam_i, mu_i in zip(lam, mu, strict=True)]

            for k, w in zip(keys, new_lam, strict=True):
                active[k] = active[k]._replace(weight=w)
            removed = [k for k, w in zip(keys, new_lam, strict=True) if w == 0]
            for k in removed:
                if verbose:
                    print(f"  evicted: {active[k].cons}")
                del active[k]
            active_set_removals += len(removed)
        else:
            raise RuntimeError(
                f"Wolfe's algorithm's minor cycle failed to converge in {max_minor} iterations."
            )

        x = _weighted_sum(active, m)

    raise RuntimeError(f"Wolfe's algorithm failed to converge in {max_major} major iterations.")
