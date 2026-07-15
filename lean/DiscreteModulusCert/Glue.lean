import DiscreteModulusCert.Family

/-!
# Gluing pmfs across a restriction/contraction split

The certificate's per-block local pmfs (§5.1.5/§6 of the plan document)
need composing into one pmf on the whole graph's spanning trees, via
`lean-modulus`'s gluing fact
(`Multigraph.isBase_union_of_isBase_restrict_isBase_contract`): a base `I`
of the restriction to a block `A` plus a base `J` of the contraction by
`I` unions to a base of the whole graph. `Pmf.glue` lifts this from single
bases to whole pmfs: given an independent choice of block-tree (drawn from
`μA`) and rest-of-graph-tree (drawn from `μRest`), their union is
distributed as the product measure.

**Why `μRest` is a pmf on `G.graphicMatroid ／ A` (contraction by the whole
block), not `G.graphicMatroid ／ I` for a specific tree `I`.** The gluing
fact needs a base of `M ／ I` for the *specific* `I` drawn from `μA` — a
priori a different matroid for each `I`. But contracting a block to a
point is fundamentally about which *vertices* got merged, not which
spanning tree justified the contraction, so bases of `M ／ I` disjoint
from `A` are exactly bases of `M ／ A`, for *any* basis `I` of the block
— `isBase_contract_iff_of_isBasis_restrict` below proves this directly
from Mathlib's matroid contraction API
(`IsBasis'.contract_eq_contract_delete`, plus the fact that `A \ I` are
all loops of `M ／ I`), no graph-specific argument needed. So a single
`μRest : Pmf (M ／ A)` is simultaneously valid against `M ／ I` for every
`I` in `μA`'s support, and `Pmf.glue` never has to assume that as a
hypothesis.
-/

namespace DiscreteModulusCert

open scoped Matroid
open Multigraph Classical

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

section Glue

variable {A : Set E}

/-- The loops created by contracting a block by one of its own bases are
exactly the rest of the block: an element of `A` not in the chosen basis
`I` can never be independently added to `I`, by `I`'s maximality as a
basis of `A`. -/
private theorem isLoop_contract_of_mem_sdiff {I : Set E}
    (hI : (G.graphicMatroid ↾ A).IsBase I) {a : E} (ha : a ∈ A \ I) :
    (G.graphicMatroid ／ I).IsLoop a := by
  have hIbasis : G.graphicMatroid.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  have hIindep : G.graphicMatroid.Indep I := hIbasis.indep
  have hg : a ∈ (G.graphicMatroid ／ I).E := by
    rw [Matroid.contract_ground, Multigraph.graphicMatroid_E]
    exact ⟨Set.mem_univ a, ha.2⟩
  by_contra hnl
  rw [Matroid.not_isLoop_iff hg, ← Matroid.indep_singleton, hIindep.contract_indep_iff] at hnl
  obtain ⟨_, hind⟩ := hnl
  have heq := hIbasis.eq_of_subset_indep hind Set.subset_union_right
    (Set.union_subset (Set.singleton_subset_iff.mpr ha.1) hIbasis.subset)
  exact ha.2 (heq ▸ Set.mem_union_left I rfl)

/-- **Contraction by a block doesn't care which of the block's own trees
justified it.** For `I` a basis (spanning tree) of the block `A`,
contracting by `I` and contracting by the whole block `A` have the same
bases outside `A` — a general matroid fact (via
`IsBasis'.contract_eq_contract_delete`: contracting by `A` is the same as
contracting by `I` and then deleting `A \ I`, and deleting the loops
`A \ I` creates doesn't change which disjoint sets are bases). This is
exactly the "shrinking a block to a point is about which vertices merge,
not which spanning tree justified it" fact `Pmf.glue` relies on. -/
theorem isBase_contract_iff_of_isBasis_restrict {I : Set E}
    (hI : (G.graphicMatroid ↾ A).IsBase I) {T : Set E} (hT : Disjoint T A) :
    (G.graphicMatroid ／ A).IsBase T ↔ (G.graphicMatroid ／ I).IsBase T := by
  have hIbasis : G.graphicMatroid.IsBasis' I A := Matroid.isBase_restrict_iff'.mp hI
  rw [hIbasis.contract_eq_contract_delete, Matroid.delete_isBase_iff]
  constructor
  · intro hbasis
    refine hbasis.isBase_of_spanning ?_
    rw [Matroid.spanning_iff_ground_subset_closure]
    intro x hx
    by_cases hxD : x ∈ A \ I
    · exact (isLoop_contract_of_mem_sdiff G hI hxD).mem_closure _
    · have hsub := (G.graphicMatroid ／ I).subset_closure ((G.graphicMatroid ／ I).E \ (A \ I))
      exact hsub ⟨hx, hxD⟩
  · intro hbase
    have hTsub : T ⊆ (G.graphicMatroid ／ I).E \ (A \ I) :=
      Set.subset_sdiff.mpr ⟨hbase.subset_ground, hT.mono_right Set.sdiff_subset⟩
    exact hbase.isBasis_of_subset (hBX := hTsub)

private theorem glue_injOn (μA : Pmf (G.graphicMatroid ↾ A)) (μRest : Pmf (G.graphicMatroid ／ A))
    (hdisj : ∀ J ∈ μRest.support, Disjoint J A) :
    Set.InjOn (fun p : Set E × Set E => p.2 ∪ p.1) (μA.support ×ˢ μRest.support : Finset (Set E × Set E)) := by
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

/-- Glue a block's tree-pmf with the (canonical, tree-independent) pmf on
the rest of the graph after shrinking that block, into a single pmf on
the whole graph's spanning trees. `hdisj` — `μRest`'s trees never touch
the block at all — is the only hypothesis needed; compatibility with
whichever tree of the block gets drawn is automatic
(`isBase_contract_iff_of_isBasis_restrict`). -/
noncomputable def Pmf.glue (μA : Pmf (G.graphicMatroid ↾ A)) (μRest : Pmf (G.graphicMatroid ／ A))
    (hdisj : ∀ J ∈ μRest.support, Disjoint J A) :
    Pmf G.graphicMatroid where
  support := (μA.support ×ˢ μRest.support).image (fun p => p.2 ∪ p.1)
  weight := fun T =>
    ∑ p ∈ μA.support ×ˢ μRest.support, if p.2 ∪ p.1 = T then μA.weight p.1 * μRest.weight p.2 else 0
  isBase := by
    intro T hT
    obtain ⟨⟨I, J⟩, hp, hTeq⟩ := Finset.mem_image.mp hT
    rw [Finset.mem_product] at hp
    have hI : (G.graphicMatroid ↾ A).IsBase I := μA.isBase I hp.1
    have hJ : (G.graphicMatroid ／ I).IsBase J :=
      (isBase_contract_iff_of_isBasis_restrict G hI (hdisj J hp.2)).mp (μRest.isBase J hp.2)
    simpa [← hTeq] using G.isBase_union_of_isBase_restrict_isBase_contract hI hJ
  nonneg := by
    intro T _
    refine Finset.sum_nonneg fun p hp => ?_
    rw [Finset.mem_product] at hp
    split
    · exact mul_nonneg (μA.nonneg p.1 hp.1) (μRest.nonneg p.2 hp.2)
    · exact le_refl 0
  sum_one := by
    have hInj := glue_injOn G μA μRest hdisj
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

end Glue

end DiscreteModulusCert
