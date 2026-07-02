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
families
    Functor classes/operators implementing families of objects
    (`ShortestObjectFinder`s) for use with `algorithms.modulus`.
demo
    Small graphs and brute-force helpers for demonstrations.
protocols
    Shared result types (`ShortestResult`, `SubproblemResult`,
    `ModulusResult`) and structural interfaces (`ShortestObjectFinder`,
    `SubproblemSolver`).
"""
