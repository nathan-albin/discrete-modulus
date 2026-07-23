import Mathlib.Algebra.Order.Ring.Rat

/-!
# Kruskal's algorithm -- the accepted, unverified admissibility oracle

This project's one deliberately-accepted soundness gap: checking a density
`ρ` is admissible (every spanning tree has `ρ`-weight `≥ 1`) reduces to
checking the *minimum*-weight spanning tree's weight is `≥ 1` (if the
minimum clears the bar, every tree does; if some tree didn't, it couldn't
be less than the true minimum). Finding that minimum is exactly what
Kruskal's algorithm computes -- but this implementation's output is not
proven to *actually* be a minimum spanning tree; the checker only runs it
and trusts the result. That is the whole content of the gap; nothing here
tries to paper over it.

Because this computation's *correctness* is out of scope for what Lean
checks (by design -- a real, planned follow-up, not an oversight), there is
no proof obligation riding on this file at all: `find`'s termination isn't
proven (a `partial def`, since proving it would need a well-formedness
invariant on the union-find array this project has no other use for), and
neither is `run` producing a genuine spanning tree. This is the same class
of trust already extended to Lean's own compiler by `native_decide`
elsewhere in this project, just made an explicit, named gap instead of an
implicit one.

See `docs/certification/trust.md` for the full trusted-computing-base
ledger and the status of proving this algorithm correct as a follow-up. -/

namespace DiscreteModulusCert
namespace Kruskal

/-- Follows `parent` pointers to a set's representative. No path
compression: simplicity over speed, since this whole computation is
already outside what Lean verifies (see the file docstring) -- there is no
proof benefit to a faster version, only a speed one, and Kruskal's
comparison-sort step already dominates asymptotically. `partial`: proving
termination needs an invariant (e.g. `parent`'s "root chain length
strictly decreases") this file has no other use for, and is moot anyway
given the whole computation is untrusted. -/
partial def find (parent : Array Nat) (x : Nat) : Nat :=
  let p := parent.getD x x
  if p = x then x else find parent p

/-- Merges `x`'s and `y`'s sets by pointing one root at the other. -/
def union (parent : Array Nat) (x y : Nat) : Array Nat :=
  parent.set! (find parent x) (find parent y)

/-- **Kruskal's greedy minimum-spanning-tree algorithm.** Given `n`
vertices, `endpoints[i]` the two endpoints of edge `i`, and `weight[i]`
edge `i`'s weight, sorts edge indices ascending by weight and greedily
keeps each edge that joins two still-separate components, threading a
union-find structure through. Returns the included edge indices. This is
this project's accepted, unverified admissibility oracle (see the file
docstring) -- its result is trusted to be a genuine minimum spanning tree
of a connected graph, not proven to be one. -/
def run (n : Nat) (endpoints : Array (Nat × Nat)) (weight : Array ℚ) : List Nat :=
  let order := (List.range endpoints.size).mergeSort
    (fun i j => decide (weight.getD i 0 ≤ weight.getD j 0))
  let rec go (parent : Array Nat) : List Nat → List Nat → List Nat
    | [], acc => acc.reverse
    | i :: rest, acc =>
        let (u, v) := endpoints.getD i (0, 0)
        if find parent u = find parent v then go parent rest acc
        else go (union parent u v) rest (i :: acc)
  go (Array.range n) order []

end Kruskal
end DiscreteModulusCert
