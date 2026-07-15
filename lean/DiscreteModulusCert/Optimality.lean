import DiscreteModulusCert.Family
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# The certificate-optimality lemma

The direct Cauchy-Schwarz argument from `Certification_Thoughts.md`
(`scratch/` in the `discrete-modulus` repo, not part of this Lean
project): for `ρ` admissible and `μ` a pmf with marginal `η`, if
`ρ = η / ‖η‖²` then `ρ` and `μ` are simultaneously optimal — `ρ` achieves
the minimum squared norm over all admissible densities (`ρ` solves the
modulus problem), and `μ` achieves the minimum squared norm of its own
marginal over all pmfs (`μ` solves the dual min-norm-point problem — the
same quantity Wolfe's algorithm computes). Both halves follow from the
same two ingredients (`Pmf.one_le_pairing_marginal_of_admissible` plus
squared Cauchy-Schwarz), just with the roles of `ρ` and the pmf's marginal
swapped.
-/

namespace DiscreteModulusCert

variable {V E : Type*} [Fintype E] {G : Multigraph V E}

private theorem sqNorm_div_const (f : E → ℚ) (c : ℚ) :
    sqNorm (fun e => f e / c) = sqNorm f / c ^ 2 := by
  simp only [sqNorm, div_pow]
  rw [← Finset.sum_div]

/-- If `ρ = η / ‖η‖²` for `‖η‖² ≠ 0`, then `‖ρ‖² * ‖η‖² = 1` — the algebraic
fact behind "`ρ` and `η/‖η‖` are parallel unit-pairing vectors" in the
Cauchy-Schwarz argument. -/
theorem sqNorm_mul_sqNorm_eq_one_of_eq_div {η ρ : CertDensity E} (hηpos : sqNorm η ≠ 0)
    (hρeq : ρ = fun e => η e / sqNorm η) : sqNorm ρ * sqNorm η = 1 := by
  rw [hρeq, sqNorm_div_const]
  field_simp

/-- **Certificate optimality, primal half**: an admissible `ρ` of the form
`η / ‖η‖²`, `η` a pmf's marginal, achieves the minimum squared norm among
*all* admissible densities. -/
theorem isMinOn_sqNorm_adm_of_certificate {ρ : CertDensity E} (_hρAdm : IsAdmissible G ρ)
    {μ : Pmf G} {η : E → ℚ} (hη : η = μ.marginal) (hηpos : sqNorm η ≠ 0)
    (hρeq : ρ = fun e => η e / sqNorm η) :
    ∀ ρ' : CertDensity E, IsAdmissible G ρ' → sqNorm ρ ≤ sqNorm ρ' := by
  intro ρ' hρ'Adm
  have h1 : (1 : ℚ) ≤ pairing ρ' η := hη ▸ Pmf.one_le_pairing_marginal_of_admissible hρ'Adm μ
  have hcs : pairing ρ' η ^ 2 ≤ sqNorm ρ' * sqNorm η := sq_pairing_le_sqNorm_mul_sqNorm ρ' η
  have h1sq : (1 : ℚ) ≤ pairing ρ' η ^ 2 := by nlinarith [h1]
  have hle : (1 : ℚ) ≤ sqNorm ρ' * sqNorm η := le_trans h1sq hcs
  have hηpos' : 0 < sqNorm η := lt_of_le_of_ne (sqNorm_nonneg η) (Ne.symm hηpos)
  have hprod : sqNorm ρ * sqNorm η = 1 := sqNorm_mul_sqNorm_eq_one_of_eq_div hηpos hρeq
  exact le_of_mul_le_mul_right (hprod.trans_le hle) hηpos'

/-- **Certificate optimality, dual half**: for `ρ` admissible of the form
`η / ‖η‖²`, `η` achieves the minimum squared norm among the marginals of
*all* pmfs on `G`'s spanning trees — exactly the quantity Wolfe's
algorithm (`min_norm_point_wolfe` in the Python builder) computes. -/
theorem isMinOn_sqNorm_marginal_of_certificate {ρ : CertDensity E} (hρAdm : IsAdmissible G ρ)
    {μ : Pmf G} {η : E → ℚ} (_hη : η = μ.marginal) (hηpos : sqNorm η ≠ 0)
    (hρeq : ρ = fun e => η e / sqNorm η) :
    ∀ μ' : Pmf G, sqNorm η ≤ sqNorm μ'.marginal := by
  intro μ'
  have h1 : (1 : ℚ) ≤ pairing ρ μ'.marginal :=
    Pmf.one_le_pairing_marginal_of_admissible hρAdm μ'
  have hcs : pairing ρ μ'.marginal ^ 2 ≤ sqNorm ρ * sqNorm μ'.marginal :=
    sq_pairing_le_sqNorm_mul_sqNorm ρ μ'.marginal
  have h1sq : (1 : ℚ) ≤ pairing ρ μ'.marginal ^ 2 := by nlinarith [h1]
  have hle : (1 : ℚ) ≤ sqNorm ρ * sqNorm μ'.marginal := le_trans h1sq hcs
  have hprod : sqNorm ρ * sqNorm η = 1 := sqNorm_mul_sqNorm_eq_one_of_eq_div hηpos hρeq
  have hρpos' : 0 < sqNorm ρ := by
    by_contra h
    push Not at h
    have h0 : sqNorm ρ = 0 := le_antisymm h (sqNorm_nonneg ρ)
    rw [h0, zero_mul] at hprod
    exact absurd hprod (by norm_num)
  exact le_of_mul_le_mul_left (hprod.trans_le hle) hρpos'

/-- **Certificate optimality.** If `ρ` is admissible for `G`'s spanning
trees, `μ` is a pmf on `G`'s spanning trees with marginal `η`, and
`ρ = η / ‖η‖²`, then `ρ` and `μ` are simultaneously optimal: `ρ` solves the
modulus problem (minimizes squared norm over admissible densities) and `μ`
solves its dual (minimizes the squared norm of its own marginal over all
pmfs). This is the theorem PR 5's verifier ultimately invokes: parse a
certificate's `ρ`, `μ`, `η`, check the three hypotheses below in `ℚ`
(admissibility via the Kruskal oracle, §5.2; `hη`/`hηpos`/`hρeq` purely
arithmetic), and conclude both halves of optimality. -/
theorem certificate_optimality {ρ : CertDensity E} (hρAdm : IsAdmissible G ρ)
    {μ : Pmf G} {η : E → ℚ} (hη : η = μ.marginal) (hηpos : sqNorm η ≠ 0)
    (hρeq : ρ = fun e => η e / sqNorm η) :
    (∀ ρ' : CertDensity E, IsAdmissible G ρ' → sqNorm ρ ≤ sqNorm ρ') ∧
      (∀ μ' : Pmf G, sqNorm η ≤ sqNorm μ'.marginal) :=
  ⟨isMinOn_sqNorm_adm_of_certificate hρAdm hη hηpos hρeq,
    isMinOn_sqNorm_marginal_of_certificate hρAdm hη hηpos hρeq⟩

/-- **Admissibility definitional lemma.** `ρ` is admissible for `G` iff
every spanning tree of `G` has `ρ`-weight at least `1` — genuinely
definitional (`IsAdmissible` is stated exactly this way), kept as a named,
discoverable lemma since it's the hinge PR 5's admissibility check
actually invokes. The further equivalence to "the *minimum* spanning-tree
weight is `≥ 1`" (the form that literally matches a Kruskal computation's
output, §5.2) needs the minimum to be attained — deferred until PR 5
actually wires in a Kruskal implementation to compute against. -/
theorem isAdmissible_iff_one_le_pairing_spanningTreeUsage {ρ : CertDensity E} :
    IsAdmissible G ρ ↔ ∀ T : Set E, G.IsSpanningTree T → 1 ≤ pairing ρ (spanningTreeUsage T) :=
  Iff.rfl

end DiscreteModulusCert
