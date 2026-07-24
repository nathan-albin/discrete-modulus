import DiscreteModulusCert.ForestDecide

/-!
Smoke test for `instDecidableIsForestOfList` (`ForestDecide.lean`) on a
concrete 3-cycle: confirms the instance distinguishes forests from
non-forests, handles a duplicated edge index idempotently, and rejects a
loop, rather than just type-checking vacuously.

**Why `native_decide`, not `decide`.** `decide` gets stuck partway through
kernel reduction, not because of anything in `ForestDecide.lean`, but
because Mathlib's own `Reachable` decidability instance
(`SimpleGraph.instDecidableRelReachable`,
`Combinatorics/SimpleGraph/Connectivity/Finite.lean`) is built via
`decidable_of_iff'` from a `propext`-cast proof, which the kernel's `decide`
evaluator can't unfold (a well-documented Lean 4 phenomenon, independent of
this project). `native_decide` compiles to native code instead of reducing
in the kernel, so it isn't affected by this, at the standard cost of
trusting the compiler (`Lean.ofReduceBool`) rather than the kernel for this
particular check. This is the same trade-off any Lean project makes when
running a `Decidable` instance whose witness doesn't kernel-reduce
directly: the instance's existence and correctness are still fully
kernel-checked, with no `sorry`, independent of which tactic evaluates it
here.
-/

namespace DiscreteModulusCert.ForestDecideTest

-- Triangle: 3 vertices, 3 edges (0-1, 1-2, 2-0).
private def endpoints : Fin 3 → Sym2 (Fin 3)
  | 0 => s(0, 1)
  | 1 => s(1, 2)
  | 2 => s(2, 0)

private def G : Multigraph (Fin 3) (Fin 3) := ⟨endpoints⟩

/-- Two edges of the triangle: a forest (a path). -/
example : G.IsForest ({e | e ∈ ([0, 1] : List (Fin 3))} : Set (Fin 3)) := by native_decide

/-- All three edges: contains the triangle's cycle, not a forest. -/
example : ¬ G.IsForest ({e | e ∈ ([0, 1, 2] : List (Fin 3))} : Set (Fin 3)) := by native_decide

/-- A single edge: trivially a forest. -/
example : G.IsForest ({e | e ∈ ([0] : List (Fin 3))} : Set (Fin 3)) := by native_decide

/-- A repeated edge index (idempotent insertion): still just a path, still a forest. -/
example : G.IsForest ({e | e ∈ ([0, 1, 0] : List (Fin 3))} : Set (Fin 3)) := by native_decide

private def loopEndpoints : Fin 1 → Sym2 (Fin 3)
  | 0 => s(0, 0)

private def GLoop : Multigraph (Fin 3) (Fin 1) := ⟨loopEndpoints⟩

/-- A single loop edge is never a forest. -/
example : ¬ GLoop.IsForest ({e | e ∈ ([0] : List (Fin 1))} : Set (Fin 1)) := by native_decide

end DiscreteModulusCert.ForestDecideTest
