import LeanModulus.Common.Multigraph
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat

/-!
# A `ℚ`-native density / admissibility / pmf vocabulary

`lean-modulus`'s own `Density`/`FamilyOfObjects`/`Adm`
(`LeanModulus.Common.FamilyOfObjects`) are valued in `ℝ≥0`, which has no
subtraction: Mathlib's finite Cauchy-Schwarz inequality
(`Finset.sum_mul_sq_le_sq_mul_sq`) needs a genuine ordered *ring* and
doesn't apply to it directly. `lean-modulus`'s own duality proof
(`Common/Duality.lean`) works around this by detouring through `ℝ` via
`Density.toReal`, plus real-analysis machinery (compactness, extreme
points) this certificate doesn't need. Since certificate values are exact
rationals throughout, it's simpler to define a small self-contained
`ℚ`-valued vocabulary here instead — reusing only the graph/matroid layer
(`Multigraph`, `IsSpanningTree`), which doesn't mention densities at all.
-/

namespace DiscreteModulusCert

open Multigraph

variable {V E : Type*} [Fintype E]

/-- A density assigning a rational cost to each edge. -/
abbrev CertDensity (E : Type*) := E → ℚ

/-- The pairing `⟨f, g⟩ = ∑ e, f e * g e`. -/
def pairing (f g : E → ℚ) : ℚ := ∑ e, f e * g e

/-- The squared norm `‖f‖² = ∑ e, f e ^ 2`. -/
def sqNorm (f : E → ℚ) : ℚ := ∑ e, f e ^ 2

theorem pairing_comm (f g : E → ℚ) : pairing f g = pairing g f := by
  simp [pairing, mul_comm]

theorem pairing_self (f : E → ℚ) : pairing f f = sqNorm f := by
  simp [pairing, sqNorm, sq]

theorem sqNorm_nonneg (f : E → ℚ) : 0 ≤ sqNorm f :=
  Finset.sum_nonneg fun e _ => sq_nonneg (f e)

/-- **Cauchy-Schwarz**, squared form (no square roots needed, so this stays
in `ℚ` throughout): a direct specialization of Mathlib's
`Finset.sum_mul_sq_le_sq_mul_sq`. -/
theorem sq_pairing_le_sqNorm_mul_sqNorm (f g : E → ℚ) :
    pairing f g ^ 2 ≤ sqNorm f * sqNorm g :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g

/-- The `{0, 1}`-indicator usage vector of an edge set `T`. -/
noncomputable def spanningTreeUsage (T : Set E) : E → ℚ := T.indicator (fun _ => 1)

open Classical in
omit [Fintype E] in
theorem spanningTreeUsage_apply (T : Set E) (e : E) :
    spanningTreeUsage T e = if e ∈ T then 1 else 0 := by
  simp [spanningTreeUsage, Set.indicator_apply]

/-- A density `ρ` is admissible for `G` if every spanning tree of `G` has
`ρ`-weight at least `1`. -/
def IsAdmissible (G : Multigraph V E) (ρ : CertDensity E) : Prop :=
  ∀ T : Set E, G.IsSpanningTree T → 1 ≤ pairing ρ (spanningTreeUsage T)

/-- The admissible set of densities for `G`. -/
def Adm (G : Multigraph V E) : Set (CertDensity E) := {ρ | IsAdmissible G ρ}

/-- A finitely-supported probability distribution on the spanning trees of
`G`, with exact rational weights — the shape a certificate's per-block
local pmf actually serializes as (a `Finset` of edge sets plus a rational
weight each). -/
structure Pmf (G : Multigraph V E) where
  /-- The trees in the support of the distribution. -/
  support : Finset (Set E)
  /-- The weight assigned to each tree (only meaningful on `support`). -/
  weight : Set E → ℚ
  /-- Every tree in the support is genuinely a spanning tree of `G`. -/
  isSpanningTree : ∀ T ∈ support, G.IsSpanningTree T
  /-- Weights are nonnegative. -/
  nonneg : ∀ T ∈ support, 0 ≤ weight T
  /-- Weights sum to `1`. -/
  sum_one : ∑ T ∈ support, weight T = 1

namespace Pmf

variable {G : Multigraph V E}

/-- The expected usage vector `𝒩ᵀμ`. -/
noncomputable def marginal (μ : Pmf G) (e : E) : ℚ :=
  ∑ T ∈ μ.support, μ.weight T * spanningTreeUsage T e

/-- Pairing against a marginal distributes over the pmf's support: this is
the algebraic heart of the certificate-optimality argument, turning a
statement about the aggregate marginal into one about individual trees,
where admissibility actually applies. -/
theorem pairing_marginal (μ : Pmf G) (ρ : CertDensity E) :
    pairing ρ μ.marginal = ∑ T ∈ μ.support, μ.weight T * pairing ρ (spanningTreeUsage T) := by
  unfold pairing marginal
  calc ∑ e, ρ e * ∑ T ∈ μ.support, μ.weight T * spanningTreeUsage T e
      = ∑ e, ∑ T ∈ μ.support, ρ e * (μ.weight T * spanningTreeUsage T e) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ T ∈ μ.support, ∑ e, ρ e * (μ.weight T * spanningTreeUsage T e) := Finset.sum_comm
    _ = ∑ T ∈ μ.support, μ.weight T * ∑ e, ρ e * spanningTreeUsage T e := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- If `ρ` is admissible and `μ` is a pmf on `G`'s spanning trees, `ρ`'s
pairing against `μ`'s marginal is at least `1` — the expectation, over
`μ`, of the per-tree admissibility bound. -/
theorem one_le_pairing_marginal_of_admissible {ρ : CertDensity E} (hρ : IsAdmissible G ρ)
    (μ : Pmf G) : 1 ≤ pairing ρ μ.marginal := by
  rw [pairing_marginal]
  calc (1 : ℚ) = ∑ T ∈ μ.support, μ.weight T := μ.sum_one.symm
    _ ≤ ∑ T ∈ μ.support, μ.weight T * pairing ρ (spanningTreeUsage T) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have h1 : 1 ≤ pairing ρ (spanningTreeUsage T) := hρ T (μ.isSpanningTree T hT)
        have h0 : 0 ≤ μ.weight T := μ.nonneg T hT
        calc μ.weight T = μ.weight T * 1 := (mul_one _).symm
          _ ≤ μ.weight T * pairing ρ (spanningTreeUsage T) := mul_le_mul_of_nonneg_left h1 h0

end Pmf

end DiscreteModulusCert
