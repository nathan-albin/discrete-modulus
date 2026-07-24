import LeanModulus.Common.GraphicMatroid
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Rat

/-!
# A `ℚ`-native density / admissibility / pmf vocabulary

`lean-modulus`'s own `Density`/`FamilyOfObjects`/`Adm`
(`LeanModulus.Common.FamilyOfObjects`) are valued in `ℝ≥0`, which has no
subtraction: Mathlib's finite Cauchy-Schwarz inequality
(`Finset.sum_mul_sq_le_sq_mul_sq`) needs an ordered *ring* and doesn't
apply to it directly. `lean-modulus`'s own duality proof
(`Common/Duality.lean`) works around this by detouring through `ℝ` via
`Density.toReal`, plus real-analysis machinery (compactness, extreme
points) this certificate doesn't need. Since certificate values are exact
rationals throughout, it's simpler to define a small self-contained
`ℚ`-valued vocabulary here instead.

Stated over an arbitrary `Matroid E` (bases), not `Multigraph`/
`IsSpanningTree` directly: the certificate's gluing step (`Glue.lean`)
composes pmfs across a matroid restriction/contraction split (`M ↾ A`,
`M ／ I`), and neither `M ↾ A` nor `M ／ I` is obviously "the graphic
matroid of some other multigraph" without extra graph theory this project
doesn't otherwise need. Working with `Matroid` throughout sidesteps that
entirely. The graph-specific interpretation ("`M = G.graphicMatroid`, `G`
connected, so a base is exactly a spanning tree") is a thin corollary at
the bottom of this file, via `lean-modulus`'s `isSpanningTree_iff_isBase`.
-/

namespace DiscreteModulusCert

open scoped Matroid

variable {E : Type*} [Fintype E]

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

/-- The `{0, 1}`-indicator usage vector of an edge set: a base's own usage
vector when `T` is a base of the matroid in play, but the definition
itself doesn't care. -/
noncomputable def usageVector (T : Set E) : E → ℚ := T.indicator (fun _ => 1)

open Classical in
omit [Fintype E] in
theorem usageVector_apply (T : Set E) (e : E) :
    usageVector T e = if e ∈ T then 1 else 0 := by
  simp [usageVector, Set.indicator_apply]

/-- A density `ρ` is admissible for a matroid `M` if every base of `M` has
`ρ`-weight at least `1`. -/
def IsAdmissible (M : Matroid E) (ρ : CertDensity E) : Prop :=
  ∀ T : Set E, M.IsBase T → 1 ≤ pairing ρ (usageVector T)

/-- The admissible set of densities for `M`. -/
def Adm (M : Matroid E) : Set (CertDensity E) := {ρ | IsAdmissible M ρ}

/-- A finitely-supported probability distribution on the bases of `M`,
with exact rational weights: the shape a certificate's per-block local pmf
serializes as (a `Finset` of edge sets plus a rational weight each). -/
structure Pmf (M : Matroid E) where
  /-- The bases in the support of the distribution. -/
  support : Finset (Set E)
  /-- The weight assigned to each base (only meaningful on `support`). -/
  weight : Set E → ℚ
  /-- Every element of the support is a base of `M`. -/
  isBase : ∀ T ∈ support, M.IsBase T
  /-- Weights are nonnegative. -/
  nonneg : ∀ T ∈ support, 0 ≤ weight T
  /-- Weights sum to `1`. -/
  sum_one : ∑ T ∈ support, weight T = 1

namespace Pmf

variable {M : Matroid E}

/-- The expected usage vector `𝒩ᵀμ`. -/
noncomputable def marginal (μ : Pmf M) (e : E) : ℚ :=
  ∑ T ∈ μ.support, μ.weight T * usageVector T e

/-- Pairing against a marginal distributes over the pmf's support: this is
the algebraic heart of the certificate-optimality argument, turning a
statement about the aggregate marginal into one about individual bases,
where admissibility actually applies. -/
theorem pairing_marginal (μ : Pmf M) (ρ : CertDensity E) :
    pairing ρ μ.marginal = ∑ T ∈ μ.support, μ.weight T * pairing ρ (usageVector T) := by
  unfold pairing marginal
  calc ∑ e, ρ e * ∑ T ∈ μ.support, μ.weight T * usageVector T e
      = ∑ e, ∑ T ∈ μ.support, ρ e * (μ.weight T * usageVector T e) := by
        simp_rw [Finset.mul_sum]
    _ = ∑ T ∈ μ.support, ∑ e, ρ e * (μ.weight T * usageVector T e) := Finset.sum_comm
    _ = ∑ T ∈ μ.support, μ.weight T * ∑ e, ρ e * usageVector T e := by
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- If `ρ` is admissible and `μ` is a pmf on `M`'s bases, `ρ`'s pairing
against `μ`'s marginal is at least `1`: the expectation, over `μ`, of the
per-base admissibility bound. -/
theorem one_le_pairing_marginal_of_admissible {ρ : CertDensity E} (hρ : IsAdmissible M ρ)
    (μ : Pmf M) : 1 ≤ pairing ρ μ.marginal := by
  rw [pairing_marginal]
  calc (1 : ℚ) = ∑ T ∈ μ.support, μ.weight T := μ.sum_one.symm
    _ ≤ ∑ T ∈ μ.support, μ.weight T * pairing ρ (usageVector T) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have h1 : 1 ≤ pairing ρ (usageVector T) := hρ T (μ.isBase T hT)
        have h0 : 0 ≤ μ.weight T := μ.nonneg T hT
        calc μ.weight T = μ.weight T * 1 := (mul_one _).symm
          _ ≤ μ.weight T * pairing ρ (usageVector T) := mul_le_mul_of_nonneg_left h1 h0

end Pmf

/-! ## Graph interpretation

For a *connected* multigraph `G`, `G.graphicMatroid`'s bases are exactly
its spanning trees (`Multigraph.isSpanningTree_iff_isBase`), so
`IsAdmissible`/`Pmf` over `G.graphicMatroid` mean exactly "admissible for
`G`" / "a pmf on `G`'s spanning trees." -/

theorem isAdmissible_graphicMatroid_iff {V : Type*} (G : Multigraph V E)
    (hGconn : (G.toSimpleGraph Set.univ).Connected) {ρ : CertDensity E} :
    IsAdmissible G.graphicMatroid ρ ↔
      ∀ T : Set E, G.IsSpanningTree T → 1 ≤ pairing ρ (usageVector T) := by
  unfold IsAdmissible
  constructor
  · exact fun h T hT => h T ((G.isSpanningTree_iff_isBase hGconn).mp hT)
  · exact fun h T hT => h T ((G.isSpanningTree_iff_isBase hGconn).mpr hT)

end DiscreteModulusCert
