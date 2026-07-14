"""
discrete_modulus: reference implementations of algorithms for discrete
modulus, a combinatorial/optimization-based generalization of the
classical modulus of curve families.

See the companion book for the underlying theory:
https://nathan-albin.com/discrete-modulus/

Modules
-------
algorithms
    The core solvers: `matrix_modulus` (direct LP) and `modulus` (the
    incremental "basic algorithm").
core_deflation
    Minimal-core detection (via exact-integer max-flow) and the
    recursive deflation sequence for homogeneous-but-not-strictly-
    homogeneous graphs -- separates a shrunk multigraph into rigid
    pieces with no forbidden trees, safe to hand to
    `min_norm_point.min_norm_point_wolfe`.
families
    Functor classes/operators implementing families of objects
    (`ShortestObjectFinder`s) for use with `algorithms.modulus`.
demo
    Small graphs and brute-force helpers for demonstrations.
min_norm_point
    Away-step Frank-Wolfe and Wolfe's (1976) minimum-norm-point algorithm:
    exact-arithmetic pmf construction on conv(Gamma) given a
    `ShortestObjectFinder` oracle.
pmf_construction
    Builds an exact pmf on spanning trees of a homogeneous shrunk
    (multi)graph: deflates it via `core_deflation`, runs
    `min_norm_point_wolfe` on each resulting piece, and represents the
    result as a factored pmf (independent local pmfs plus edge
    provenance) rather than a flat list over the whole graph's spanning
    trees.
protocols
    Shared result types (`ShortestResult`, `SubproblemResult`,
    `ModulusResult`) and structural interfaces (`ShortestObjectFinder`,
    `SubproblemSolver`).
spanning_tree_modulus
    Cunningham's algorithm: an exact, combinatorial solver
    (`spanning_tree_modulus`) specific to the spanning-tree/
    feasible-partition case, as an alternative to the general, iterative
    `algorithms.modulus`.
"""
