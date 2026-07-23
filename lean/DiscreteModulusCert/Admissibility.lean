import DiscreteModulusCert.Kruskal
import DiscreteModulusCert.Family

/-!
# The Kruskal-admissibility trust boundary, as a named axiom

This project's one accepted soundness gap: `Kruskal.run`'s output is
trusted, not proven, to be a genuine minimum-weight base of the graphic
matroid. `CertChecker.lean` already *uses* that trust
(computing a density's admissibility via Kruskal's MST weight), but only as
an ordinary runtime `Bool` check -- nothing marks *where* the trust actually
enters the kernel-checked side. This file makes that boundary an explicit
Lean `axiom`, so it shows up by name under `#print axioms` for any
certificate whose `rho` isn't uniform.

**No connectedness hypothesis.** `IsAdmissible`/`Pmf` (`Family.lean`) are
stated purely over an abstract `Matroid E`, with no reference to graph
connectivity. Kruskal's algorithm, exactly as coded in `Kruskal.lean` (sort
edges ascending by weight, greedily keep each that joins two still-separate
union-find components), is the general matroid-greedy algorithm for the
graphic matroid -- it produces a genuine minimum-weight *base* (a spanning
forest, one tree per component) whether or not the graph is connected. So
this axiom never needs to establish or assume `G` is connected.

**The complementary fact: when you don't need this axiom at all.**
`isAdmissible_const_div_ncard_of_isBase` below shows a *uniform* density
is admissible directly from a basic matroid fact (every base has the same
cardinality), with no MST oracle anywhere -- the case `house`'s certificate
falls into (`rho = 1/4` on every edge), used by `EndToEndTest.lean` to
build a fully axiom-free optimality proof for it. See
`docs/certification/trust.md`. -/

namespace DiscreteModulusCert

open scoped Matroid
open Multigraph

/-- The multigraph built from an explicit endpoints array -- the same
one-line construction `CertChecker.CheckedGraph.toMultigraph` uses,
defined standalone here (rather than importing `CertChecker`, which would
create an import cycle once `Soundness.lean` imports both this file and
`CertChecker`). -/
def mkMultigraph (n : Nat) (endpoints : Array (Fin n × Fin n)) :
    Multigraph (Fin n) (Fin endpoints.size) :=
  ⟨fun e => s(endpoints[e].1, endpoints[e].2)⟩

section UniformAdmissibility
variable {E : Type*} [Fintype E]

open Classical in
/-- Pairing a constant density against any edge set's usage vector is just
the constant times that set's cardinality. -/
theorem pairing_const_usageVector_eq (c : ℚ) (T : Set E) :
    pairing (fun _ => c) (usageVector T) = c * T.ncard := by
  show (∑ e : E, c * usageVector T e) = c * T.ncard
  simp only [usageVector_apply]
  rw [← Finset.mul_sum, Finset.sum_boole, Set.filter_mem_univ_eq_toFinset,
    ← Set.ncard_eq_toFinset_card']

/-- **A uniform density is admissible whenever you know one base's size --
no MST oracle needed.** Every base of a matroid has the same cardinality
(`Matroid.IsBase.ncard_eq_ncard_of_isBase`), so fixing one known base
`T₀`'s size pins down every other base's pairing against the uniform
density `1 / T₀.ncard` to exactly `1`. This is the complementary fact to
`Kruskal.run_isAdmissible_of_weight_ge_one` below: for a certificate whose
optimal density happens to be uniform, admissibility follows directly
from this, with no unverified oracle anywhere. -/
theorem isAdmissible_const_div_ncard_of_isBase {M : Matroid E} {T₀ : Set E}
    (hT₀ : M.IsBase T₀) (hn : T₀.ncard ≠ 0) :
    IsAdmissible M (fun _ => (1 : ℚ) / T₀.ncard) := by
  intro T hT
  rw [pairing_const_usageVector_eq, hT.ncard_eq_ncard_of_isBase hT₀,
    div_mul_cancel₀ (1 : ℚ) (Nat.cast_ne_zero.mpr hn)]

end UniformAdmissibility

namespace Kruskal

/-- **This project's accepted, unverified admissibility oracle, as a named
axiom.** Bridges "Kruskal's computed minimum-spanning-forest weight is
`≥ 1`" directly to `IsAdmissible`, at exactly the granularity needed
(bridging the computed weight to admissibility, not decomposed further
into "Kruskal computes a genuine minimum base" plus a separate logical
step) -- this is the one place trust enters the kernel-checked side for a
certificate whose `rho` isn't uniform. `endpoints : Array (Fin n × Fin n)`
matches
`CheckedGraph`'s own shape exactly, so applying this axiom at a
`CertChecker` call site only needs one small value-level bridging lemma
(`Soundness.lean`), not a graph rebuild. -/
axiom run_isAdmissible_of_weight_ge_one
    {n : Nat} (endpoints : Array (Fin n × Fin n)) (weight : Array ℚ)
    (hmin : 1 ≤ (Kruskal.run n (endpoints.map fun p => (p.1.val, p.2.val)) weight).foldl
      (fun acc i => acc + weight.getD i 0) 0) :
    IsAdmissible (mkMultigraph n endpoints).graphicMatroid
      (fun e : Fin endpoints.size => weight.getD e.val 0)

end Kruskal
end DiscreteModulusCert
