import DiscreteModulusCert.Family

/-!
# Gluing pmfs across a whole laminar family of blocks

The certificate's per-block local pmfs (§5.1.5/§6 of the plan document)
need composing into one pmf on the whole graph's spanning trees. §6
(reading the actual builder/solver-trace code, not re-deriving from
prose) found that the whole multi-round, multi-core laminar family
reduces to *one flat, ordered list* of blocks, verified by a single fold
— not a tree needing general recursion. This file provides:

* `isBase_union_of_isBase_restrict_isBase_contract` /
  `isBase_contract_iff_of_isBasis_restrict`: the two matroid facts behind
  gluing, generalized from `lean-modulus`'s graphic-matroid-specific
  versions to an arbitrary ambient `Matroid E` — needed because folding a
  *list* of blocks means gluing against intermediate ambients (`M ↾ X` for
  various `X`), not just the top-level `M` itself.
* `Pmf.glue`: lifts the single-basis gluing fact to whole pmfs, given an
  ambient `N`, a block `A ⊆ N.E`, a pmf on the block's own bases, and a
  pmf on the *canonical* (tree-independent) rest-of-`N`-after-contracting-`A`.
* `Piece`/`PieceList`/`PieceList.glueAll`: the flat-list fold itself. A
  `PieceList N U` is an ordered sequence of blocks whose edges union to
  `U`, each block's pmf typed relative to everything *before* it in the
  list (already contracted away) — exactly the shape `pmf_construction.py`
  produces (§6). `glueAll` folds it into a single `Pmf (N ↾ U)`.
-/

namespace DiscreteModulusCert

open scoped Matroid
open Classical

variable {E : Type*} [Fintype E] {N : Matroid E} {A : Set E}

omit [Fintype E] in
/-- **The gluing fact, generalized to an arbitrary ambient matroid.** A
base `I` of the restriction to a block `A` plus a base `J` of the
contraction by `I` unions to a base of the whole (ambient) matroid `N`.
Generalizes `Multigraph.isBase_union_of_isBase_restrict_isBase_contract`
(fixed to `N = G.graphicMatroid`) — needed here because folding a *list*
of blocks glues against intermediate ambients `G.graphicMatroid ↾ X`, not
just the top-level matroid itself. Proved the same way `lean-modulus`
proves its version: a thin specialization of Mathlib's general
`Matroid.Indep.union_isBasis_union_of_contract_isBasis`. -/
theorem isBase_union_of_isBase_restrict_isBase_contract (hAE : A ⊆ N.E) {I J : Set E}
    (hI : (N ↾ A).IsBase I) (hJ : (N ／ I).IsBase J) : N.IsBase (J ∪ I) := by
  have hIbasis : N.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  have hIindep : N.Indep I := hIbasis.indep
  have hJbasis : (N ／ I).IsBasis J (N ／ I).E := Matroid.isBasis_ground_iff.mpr hJ
  have hunion := hIindep.union_isBasis_union_of_contract_isBasis hJbasis
  have hEeq : (N ／ I).E ∪ I = N.E := by
    rw [Matroid.contract_ground, Set.sdiff_union_of_subset (hIbasis.subset.trans hAE)]
  rw [hEeq, Matroid.isBasis_ground_iff] at hunion
  exact hunion

omit [Fintype E] in
/-- The loops created by contracting a block by one of its own bases are
exactly the rest of the block: an element of `A` not in the chosen basis
`I` can never be independently added to `I`, by `I`'s maximality as a
basis of `A`. -/
private theorem isLoop_contract_of_mem_sdiff (hAE : A ⊆ N.E) {I : Set E}
    (hI : (N ↾ A).IsBase I) {a : E} (ha : a ∈ A \ I) : (N ／ I).IsLoop a := by
  have hIbasis : N.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  have hIindep : N.Indep I := hIbasis.indep
  have hg : a ∈ (N ／ I).E := by
    rw [Matroid.contract_ground]; exact ⟨hAE ha.1, ha.2⟩
  by_contra hnl
  rw [Matroid.not_isLoop_iff hg, ← Matroid.indep_singleton, hIindep.contract_indep_iff] at hnl
  obtain ⟨_, hind⟩ := hnl
  have heq := hIbasis.eq_of_subset_indep hind Set.subset_union_right
    (Set.union_subset (Set.singleton_subset_iff.mpr ha.1) hIbasis.subset)
  exact ha.2 (heq ▸ Set.mem_union_left I rfl)

omit [Fintype E] in
/-- **Contraction by a block doesn't care which of the block's own trees
justified it**, generalized to an arbitrary ambient matroid (see
`isBase_union_of_isBase_restrict_isBase_contract` for why the
generalization is needed). For `I` a basis (spanning tree) of the block
`A`, contracting by `I` and contracting by the whole block `A` have the
same bases outside `A` — a general matroid fact (via
`IsBasis'.contract_eq_contract_delete`: contracting by `A` is the same as
contracting by `I` and then deleting `A \ I`, and deleting the loops
`A \ I` creates doesn't change which disjoint sets are bases). -/
theorem isBase_contract_iff_of_isBasis_restrict (hAE : A ⊆ N.E) {I : Set E}
    (hI : (N ↾ A).IsBase I) {T : Set E} (hT : Disjoint T A) :
    (N ／ A).IsBase T ↔ (N ／ I).IsBase T := by
  have hIbasis : N.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  rw [hIbasis.contract_eq_contract_delete, Matroid.delete_isBase_iff]
  constructor
  · intro hbasis
    refine hbasis.isBase_of_spanning ?_
    rw [Matroid.spanning_iff_ground_subset_closure]
    intro x hx
    by_cases hxD : x ∈ A \ I
    · exact (isLoop_contract_of_mem_sdiff hAE hI hxD).mem_closure _
    · have hsub := (N ／ I).subset_closure ((N ／ I).E \ (A \ I))
      exact hsub ⟨hx, hxD⟩
  · intro hbase
    have hTsub : T ⊆ (N ／ I).E \ (A \ I) :=
      Set.subset_sdiff.mpr ⟨hbase.subset_ground, hT.mono_right Set.sdiff_subset⟩
    exact hbase.isBasis_of_subset (hBX := hTsub)

omit [Fintype E] in
private theorem glue_injOn (μA : Pmf (N ↾ A)) (μRest : Pmf (N ／ A))
    (hdisj : ∀ J ∈ μRest.support, Disjoint J A) :
    Set.InjOn (fun p : Set E × Set E => p.2 ∪ p.1)
      (μA.support ×ˢ μRest.support : Finset (Set E × Set E)) := by
  rintro ⟨I₁, J₁⟩ h₁ ⟨I₂, J₂⟩ h₂ heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at h₁ h₂
  simp only at heq
  have hI₁A : I₁ ⊆ A := by
    have h := (μA.isBase I₁ h₁.1).subset_ground; rwa [Matroid.restrict_ground_eq] at h
  have hI₂A : I₂ ⊆ A := by
    have h := (μA.isBase I₂ h₂.1).subset_ground; rwa [Matroid.restrict_ground_eq] at h
  have hJ₁A : Disjoint J₁ A := hdisj J₁ h₁.2
  have hJ₂A : Disjoint J₂ A := hdisj J₂ h₂.2
  have hIeq : I₁ = I₂ := by
    have e1 : (J₁ ∪ I₁) ∩ A = I₁ := by
      rw [Set.union_inter_distrib_right, hJ₁A.inter_eq, Set.empty_union,
        Set.inter_eq_self_of_subset_left hI₁A]
    have e2 : (J₂ ∪ I₂) ∩ A = I₂ := by
      rw [Set.union_inter_distrib_right, hJ₂A.inter_eq, Set.empty_union,
        Set.inter_eq_self_of_subset_left hI₂A]
    rw [← e1, ← e2, heq]
  have hJeq : J₁ = J₂ := by
    have hJ₁I : Disjoint J₁ I₁ := hJ₁A.mono_right hI₁A
    have hJ₂I : Disjoint J₂ I₂ := hJ₂A.mono_right hI₂A
    rw [hIeq] at hJ₁I heq
    ext x
    have hx := Set.ext_iff.mp heq x
    simp only [Set.mem_union] at hx
    constructor
    · intro h
      rcases hx.mp (Or.inl h) with h' | h'
      · exact h'
      · exact absurd h' (Set.disjoint_left.mp hJ₁I h)
    · intro h
      rcases hx.mpr (Or.inl h) with h' | h'
      · exact h'
      · exact absurd h' (Set.disjoint_left.mp hJ₂I h)
  rw [hIeq, hJeq]

/-- Glue a block's tree-pmf with the canonical (tree-independent) pmf on
the rest of the ambient matroid `N` after contracting that block, into a
single pmf on `N`'s bases. `hAE` is needed for the ambient generalization
(automatic, `Set.subset_univ`, when `N` is a connected graph's
`graphicMatroid`); `hdisj` — `μRest`'s trees never touch the block at all
— is the only hypothesis about the *pmfs themselves*; compatibility with
whichever tree of the block gets drawn is automatic
(`isBase_contract_iff_of_isBasis_restrict`). -/
noncomputable def Pmf.glue (hAE : A ⊆ N.E) (μA : Pmf (N ↾ A)) (μRest : Pmf (N ／ A))
    (hdisj : ∀ J ∈ μRest.support, Disjoint J A) :
    Pmf N where
  support := (μA.support ×ˢ μRest.support).image (fun p => p.2 ∪ p.1)
  weight := fun T =>
    ∑ p ∈ μA.support ×ˢ μRest.support, if p.2 ∪ p.1 = T then μA.weight p.1 * μRest.weight p.2 else 0
  isBase := by
    intro T hT
    obtain ⟨⟨I, J⟩, hp, hTeq⟩ := Finset.mem_image.mp hT
    rw [Finset.mem_product] at hp
    have hI : (N ↾ A).IsBase I := μA.isBase I hp.1
    have hJ : (N ／ I).IsBase J :=
      (isBase_contract_iff_of_isBasis_restrict hAE hI (hdisj J hp.2)).mp (μRest.isBase J hp.2)
    simpa [← hTeq] using isBase_union_of_isBase_restrict_isBase_contract hAE hI hJ
  nonneg := by
    intro T _
    refine Finset.sum_nonneg fun p hp => ?_
    rw [Finset.mem_product] at hp
    split
    · exact mul_nonneg (μA.nonneg p.1 hp.1) (μRest.nonneg p.2 hp.2)
    · exact le_refl 0
  sum_one := by
    have hInj := glue_injOn μA μRest hdisj
    have hsingle : ∀ p ∈ μA.support ×ˢ μRest.support,
        (∑ q ∈ μA.support ×ˢ μRest.support,
          if q.2 ∪ q.1 = p.2 ∪ p.1 then μA.weight q.1 * μRest.weight q.2 else 0)
          = μA.weight p.1 * μRest.weight p.2 := by
      intro p hp
      have hkey : (∑ q ∈ μA.support ×ˢ μRest.support,
          if q.2 ∪ q.1 = p.2 ∪ p.1 then μA.weight q.1 * μRest.weight q.2 else 0)
          = if p.2 ∪ p.1 = p.2 ∪ p.1 then μA.weight p.1 * μRest.weight p.2 else 0 :=
        Finset.sum_eq_single_of_mem p hp fun q hq hqp =>
          if_neg fun heq => hqp (hInj (Finset.mem_coe.mpr hq) (Finset.mem_coe.mpr hp) heq)
      simp at hkey
      exact hkey
    calc ∑ T ∈ (μA.support ×ˢ μRest.support).image (fun p => p.2 ∪ p.1),
          (∑ p ∈ μA.support ×ˢ μRest.support,
            if p.2 ∪ p.1 = T then μA.weight p.1 * μRest.weight p.2 else 0)
        = ∑ p ∈ μA.support ×ˢ μRest.support,
            (∑ q ∈ μA.support ×ˢ μRest.support,
              if q.2 ∪ q.1 = p.2 ∪ p.1 then μA.weight q.1 * μRest.weight q.2 else 0) :=
          Finset.sum_image (fun p hp q hq => hInj hp hq)
      _ = ∑ p ∈ μA.support ×ˢ μRest.support, μA.weight p.1 * μRest.weight p.2 :=
          Finset.sum_congr rfl hsingle
      _ = ∑ I ∈ μA.support, ∑ J ∈ μRest.support, μA.weight I * μRest.weight J :=
          Finset.sum_product' μA.support μRest.support (fun I J => μA.weight I * μRest.weight J)
      _ = ∑ I ∈ μA.support, μA.weight I * ∑ J ∈ μRest.support, μRest.weight J :=
          Finset.sum_congr rfl fun I _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ I ∈ μA.support, μA.weight I * 1 := by rw [μRest.sum_one]
      _ = ∑ I ∈ μA.support, μA.weight I := by simp
      _ = 1 := μA.sum_one

omit [Fintype E] in
open Classical in
private theorem usageVector_union_of_disjoint {I J : Set E} (hIJ : Disjoint I J) (e : E) :
    usageVector (I ∪ J) e = usageVector I e + usageVector J e := by
  simp only [usageVector_apply, Set.mem_union]
  by_cases hI : e ∈ I
  · simp [hI, Set.disjoint_left.mp hIJ hI]
  · by_cases hJ : e ∈ J <;> simp [hI, hJ]

omit [Fintype E] in
/-- **The marginal-compositionality lemma.** A glued pmf's marginal at any
edge is exactly the *sum* of the two pieces' own local marginals — never
computed from the glued pmf's (exponentially large) support directly.
This is what makes `η` cheap to derive from a certificate's per-piece
`local_pmf`s rather than from the fully-glued top-level pmf
(`Certification_Plan.md` §6's "why no top-level `eta`/`rho` fields" note):
folding this lemma down a whole `PieceList` (`PieceList.glueAll_marginal`
below) computes `η` in time linear in `pieces × edges`, never touching
the Cartesian-product blowup `Pmf.glue`'s `support` field carries.

Proved the same way `Pmf.glue`'s own `sum_one` field is: reindex the
support-image sum back to the underlying product of supports via
`glue_injOn`, then split `usageVector (J ∪ I) e` into `usageVector J e +
usageVector I e` (valid since `J`, `I` are disjoint — `J` a basis of the
contraction is disjoint from `A`, and `I ⊆ A`), and factor each half of
the resulting double sum using the two pmfs' own `sum_one` fields. -/
theorem Pmf.glue_marginal (hAE : A ⊆ N.E) (μA : Pmf (N ↾ A)) (μRest : Pmf (N ／ A))
    (hdisj : ∀ J ∈ μRest.support, Disjoint J A) (e : E) :
    (Pmf.glue hAE μA μRest hdisj).marginal e = μA.marginal e + μRest.marginal e := by
  have hInj := glue_injOn μA μRest hdisj
  have hsingle : ∀ p ∈ μA.support ×ˢ μRest.support,
      (∑ q ∈ μA.support ×ˢ μRest.support,
        if q.2 ∪ q.1 = p.2 ∪ p.1 then μA.weight q.1 * μRest.weight q.2 else 0)
        = μA.weight p.1 * μRest.weight p.2 := by
    intro p hp
    have hkey : (∑ q ∈ μA.support ×ˢ μRest.support,
        if q.2 ∪ q.1 = p.2 ∪ p.1 then μA.weight q.1 * μRest.weight q.2 else 0)
        = if p.2 ∪ p.1 = p.2 ∪ p.1 then μA.weight p.1 * μRest.weight p.2 else 0 :=
      Finset.sum_eq_single_of_mem p hp fun q hq hqp =>
        if_neg fun heq => hqp (hInj (Finset.mem_coe.mpr hq) (Finset.mem_coe.mpr hp) heq)
    simpa using hkey
  have hIJdisj : ∀ p ∈ μA.support ×ˢ μRest.support, Disjoint p.2 p.1 := by
    intro p hp
    rw [Finset.mem_product] at hp
    have hIA : p.1 ⊆ A := by
      have h := (μA.isBase p.1 hp.1).subset_ground; rwa [Matroid.restrict_ground_eq] at h
    exact (hdisj p.2 hp.2).mono_right hIA
  have hmain : (Pmf.glue hAE μA μRest hdisj).marginal e
      = ∑ p ∈ μA.support ×ˢ μRest.support,
          (μA.weight p.1 * usageVector p.1 e * μRest.weight p.2
            + μA.weight p.1 * (μRest.weight p.2 * usageVector p.2 e)) := by
    show ∑ T ∈ (μA.support ×ˢ μRest.support).image (fun p => p.2 ∪ p.1),
        (∑ p ∈ μA.support ×ˢ μRest.support,
          if p.2 ∪ p.1 = T then μA.weight p.1 * μRest.weight p.2 else 0) * usageVector T e
        = _
    rw [Finset.sum_image (fun p hp q hq => hInj hp hq)]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hsingle p hp, usageVector_union_of_disjoint (hIJdisj p hp)]
    ring
  rw [hmain, Finset.sum_add_distrib,
    Finset.sum_product' μA.support μRest.support
      (fun I J => μA.weight I * usageVector I e * μRest.weight J),
    Finset.sum_product' μA.support μRest.support
      (fun I J => μA.weight I * (μRest.weight J * usageVector J e))]
  have hterm1 : ∀ I ∈ μA.support, ∑ J ∈ μRest.support, μA.weight I * usageVector I e * μRest.weight J
      = μA.weight I * usageVector I e := by
    intro I _
    rw [← Finset.mul_sum, μRest.sum_one, mul_one]
  have hterm2 : ∀ I ∈ μA.support,
      (∑ J ∈ μRest.support, μA.weight I * (μRest.weight J * usageVector J e))
        = μA.weight I * μRest.marginal e := by
    intro I _
    rw [← Finset.mul_sum]
    rfl
  rw [Finset.sum_congr rfl hterm1, Finset.sum_congr rfl hterm2, ← Finset.sum_mul, μA.sum_one, one_mul]
  rfl

/-- The trivial pmf on the (unique) base of the empty restriction. The
base case of `PieceList.glueAll`'s fold. -/
noncomputable def trivialPmf (N : Matroid E) : Pmf (N ↾ (∅ : Set E)) where
  support := {∅}
  weight := fun _ => 1
  isBase := by
    intro T hT
    simp only [Finset.mem_singleton] at hT
    subst hT
    rw [Matroid.isBase_restrict_iff (by simp)]
    simp
  nonneg := by intro T _; norm_num
  sum_one := by simp

/-- Transport a pmf along an equality of matroids — `support`/`weight` are
unchanged (`cast_support`/`cast_weight`), only the `isBase` proof's type
changes. -/
def Pmf.cast {M M' : Matroid E} (h : M = M') (μ : Pmf M) : Pmf M' := h ▸ μ

omit [Fintype E] in
@[simp] theorem Pmf.cast_support {M M' : Matroid E} (h : M = M') (μ : Pmf M) :
    (μ.cast h).support = μ.support := by subst h; rfl

omit [Fintype E] in
@[simp] theorem Pmf.cast_weight {M M' : Matroid E} (h : M = M') (μ : Pmf M) :
    (μ.cast h).weight = μ.weight := by subst h; rfl

omit [Fintype E] in
@[simp] theorem Pmf.cast_marginal {M M' : Matroid E} (h : M = M') (μ : Pmf M) (e : E) :
    (μ.cast h).marginal e = μ.marginal e := by
  unfold Pmf.marginal
  rw [Pmf.cast_support, Pmf.cast_weight]

/-- One block in a laminar family: its own edge set `A`, together with a
pmf on its own bases *given* everything listed before it (`prev`) is
already contracted away — exactly the shape `pmf_construction.py`'s
`LocalPiece` has (a piece's own `graph`, computed on the already-shrunk
working graph, together with its `result`). -/
structure Piece (N : Matroid E) (prev : Set E) where
  /-- This block's own edge set. -/
  A : Set E
  hAE : A ⊆ (N ／ prev).E
  /-- The pmf on this block's own bases, given `prev` already contracted. -/
  pmf : Pmf ((N ／ prev) ↾ A)

/-- A flat, ordered laminar family of blocks whose edges union to `U` —
the shape §6's certificate schema settled on (a flat `pieces` array, not
a tree), matching `pmf_construction.py`'s `FactoredPmf.pieces` /
`solver_trace.hpp`'s `SolverTrace.rounds` (concatenated: within-round
deflation pieces and across-round pieces are structurally identical here,
see §6). -/
inductive PieceList (N : Matroid E) : Set E → Type _
  | nil : PieceList N ∅
  | cons {U : Set E} (tail : PieceList N U) (p : Piece N U) : PieceList N (U ∪ p.A)

/-- **The fold driver.** Processes a `PieceList` in order, gluing each
new block against everything already folded in, via `Pmf.glue` composed
with the matroid identities relating a growing restriction to the next
block's own (already-contracted) matroid
(`Matroid.restrict_restrict_eq`, `Matroid.restrict_contract_eq_contract_restrict`).
Ends with a single pmf on the bases of `N` restricted to everything the
list covers. -/
noncomputable def PieceList.glueAll {N : Matroid E} : ∀ {U : Set E}, PieceList N U → Pmf (N ↾ U)
  | _, .nil => trivialPmf N
  | _, .cons tail p => by
      rename_i U
      have hdisjAU : Disjoint p.A U := by
        have h := p.hAE
        rw [Matroid.contract_ground] at h
        exact (Set.subset_sdiff.mp h).2
      have hUsub : U ⊆ (N ↾ (U ∪ p.A)).E := by
        rw [Matroid.restrict_ground_eq]; exact Set.subset_union_left
      have heqRestrict : (N ↾ (U ∪ p.A)) ↾ U = N ↾ U :=
        Matroid.restrict_restrict_eq N Set.subset_union_left
      have heqContract : (N ↾ (U ∪ p.A)) ／ U = (N ／ U) ↾ p.A := by
        rw [Matroid.restrict_contract_eq_contract_restrict _ Set.subset_union_left]
        congr 1
        rw [Set.union_sdiff_left, sdiff_eq_left.mpr hdisjAU]
      refine Pmf.glue hUsub (tail.glueAll.cast heqRestrict.symm) (p.pmf.cast heqContract.symm) ?_
      intro J hJ
      rw [Pmf.cast_support] at hJ
      have hbase := p.pmf.isBase J hJ
      have hJA : J ⊆ p.A := by
        have h := hbase.subset_ground; rwa [Matroid.restrict_ground_eq] at h
      exact hdisjAU.mono_left hJA

omit [Fintype E] in
/-- The sum of every piece's own local marginal — cheap to compute (linear
in `pieces × edges`, one small `Finset.sum` per piece), unlike
`PieceList.glueAll`'s own combined pmf, whose support is exponential in the
piece count. `PieceList.glueAll_marginal` shows this is exactly the glued
pmf's marginal, which is the entire point: it's how a certificate's
`η` gets computed at all. -/
noncomputable def PieceList.marginalSum {N : Matroid E} : ∀ {U : Set E}, PieceList N U → E → ℚ
  | _, .nil => fun _ => 0
  | _, .cons tail p => fun e => tail.marginalSum e + p.pmf.marginal e

omit [Fintype E] in
/-- Transporting a `PieceList` along an equality of its edge-set index
doesn't change its `marginalSum` — needed because a top-level certificate's
`PieceList` (e.g. `houseCertPieces`) is typically built for the *union* of
its own pieces' edges, then transported via `▸` to `Set.univ` (the
"partition-completeness" proof, `PieceList.glueAllGraph`'s own argument)
before folding. -/
theorem PieceList.marginalSum_cast {N : Matroid E} {U U' : Set E} (h : U = U')
    (l : PieceList N U) (e : E) : (h ▸ l).marginalSum e = l.marginalSum e := by
  subst h; rfl

omit [Fintype E] in
/-- **The compositional marginal theorem.** Folds `Pmf.glue_marginal` down
a whole `PieceList`: the fully-glued pmf's marginal at any edge equals the
sum of every piece's own local marginal at that edge — never the
(exponentially-support'd) glued pmf's marginal computed directly. This is
the fact that makes deriving a certificate's `η` from its `pieces` array
tractable (`Certification_Plan.md` §6). -/
theorem PieceList.glueAll_marginal {N : Matroid E} :
    ∀ {U : Set E} (l : PieceList N U) (e : E), l.glueAll.marginal e = l.marginalSum e
  | _, .nil, e => by
      show (trivialPmf N).marginal e = 0
      unfold Pmf.marginal trivialPmf
      simp [usageVector_apply]
  | _, .cons tail p, e => by
      rename_i U
      have hdisjAU : Disjoint p.A U := by
        have h := p.hAE
        rw [Matroid.contract_ground] at h
        exact (Set.subset_sdiff.mp h).2
      have hUsub : U ⊆ (N ↾ (U ∪ p.A)).E := by
        rw [Matroid.restrict_ground_eq]; exact Set.subset_union_left
      have heqRestrict : (N ↾ (U ∪ p.A)) ↾ U = N ↾ U :=
        Matroid.restrict_restrict_eq N Set.subset_union_left
      have heqContract : (N ↾ (U ∪ p.A)) ／ U = (N ／ U) ↾ p.A := by
        rw [Matroid.restrict_contract_eq_contract_restrict _ Set.subset_union_left]
        congr 1
        rw [Set.union_sdiff_left, sdiff_eq_left.mpr hdisjAU]
      have hdisj' : ∀ J ∈ (p.pmf.cast heqContract.symm).support, Disjoint J U := by
        intro J hJ
        rw [Pmf.cast_support] at hJ
        have hbase := p.pmf.isBase J hJ
        have hJA : J ⊆ p.A := by
          have h := hbase.subset_ground; rwa [Matroid.restrict_ground_eq] at h
        exact hdisjAU.mono_left hJA
      show (Pmf.glue hUsub (tail.glueAll.cast heqRestrict.symm) (p.pmf.cast heqContract.symm) hdisj').marginal e
        = tail.marginalSum e + p.pmf.marginal e
      rw [Pmf.glue_marginal, Pmf.cast_marginal, Pmf.cast_marginal, glueAll_marginal tail e]

/-- **Top-level specialization.** A `PieceList` for `G.graphicMatroid`
whose blocks cover *every* edge (`U = Set.univ`) glues into a genuine
`Pmf G.graphicMatroid` — feedable directly into `certificate_optimality`.
Requiring `U = Set.univ` at the type level is exactly §6's
"partition-completeness" check: a verifier can only produce this if the
certificate's `pieces` list, folded, is shown (e.g. by `decide` on the
concrete edge-index lists) to cover the whole graph. -/
noncomputable def PieceList.glueAllGraph {N : Matroid E} (hNE : N.E = Set.univ)
    (pieces : PieceList N Set.univ) : Pmf N :=
  pieces.glueAll.cast (hNE ▸ Matroid.restrict_ground_eq_self N)

end DiscreteModulusCert
