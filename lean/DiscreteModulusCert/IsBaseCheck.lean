import DiscreteModulusCert.Glue

/-!
# Reducing a piece's `IsBase` check to a graph forest check

§6 of the plan document left one real gap in "per-piece `IsBase`
checking": turning a certificate's raw declared tree (an edge-index list)
into a proof that it's actually a base of that piece's matroid
(`(G.graphicMatroid ／ prev) ↾ A`, in `Piece`'s language). This file
proves the reduction that makes that checkable at all:
`isBase_contract_restrict_iff_isForest` turns the matroid question into a
pure graph-combinatorics one — is a specific, small edge set a forest of
the *original* graph `G` (`Multigraph.IsForest`, no contraction/relabeling
in sight) — given one already-verified spanning tree `I₀` of everything
processed so far (`prev`).

**Resolved in `ForestDecide.lean`.** `Multigraph.IsForest` wasn't known to be
`Decidable`/computably checkable when this file was written. Its two easy
conjuncts (no loops, injective endpoints) are immediate finite checks; the
hard one, `(G.toSimpleGraph F).IsAcyclic`, is *not* decidable "for free" via
existing Mathlib instances — confirmed directly: `#synth`-style attempts at
`Decidable G.IsAcyclic` via `isAcyclic_iff_forall_isBridge` (the natural
route, since `Reachable` is decidable for `Fintype` vertex types) still fail
to synthesize, because `IsBridge`'s own decidability and a `Fintype`/`Finset`
handle on `edgeSet` aren't wired up either. `ForestDecide.lean` builds a
genuine decision procedure instead — structural recursion on a candidate
tree's edge-index list, deciding each insertion via Mathlib's
`isAcyclic_sup_fromEdgeSet_iff` — giving a real, `sorry`-free
`Decidable (G.IsForest {e | e ∈ l})` instance for any `l : List E`, which is
exactly the shape a certificate's declared tree already comes in. -/

namespace DiscreteModulusCert

open scoped Matroid
open Multigraph

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- **The matroid-to-graph reduction.** Given `I₀`, an already-verified
spanning tree of everything processed so far (`prev`), a candidate `T` for
the next piece (edges `A`, disjoint from `prev`) is a genuine base of that
piece's matroid iff (a) `I₀ ∪ T` is a forest of the *original* graph — no
contraction/relabeling needed, `I₀` being concrete data already stands in
for "`prev` contracted away" — and (b) no other edge of the piece (`A \ T`)
can be added without creating a cycle. (b) is the *single-insertion* form
of maximality (`Indep.isBase_of_forall_insert`); by the matroid exchange
property it's equivalent to full maximality, and — unlike a quantifier
over all of `A`'s independent subsets — is a check over the *finite* set
`A \ T` alone, one candidate insertion at a time. -/
theorem isBase_contract_restrict_iff_isForest {prev A I₀ T : Set E}
    (hI₀ : (G.graphicMatroid ↾ prev).IsBase I₀) (hAE : A ⊆ (G.graphicMatroid ／ prev).E)
    (hTA : T ⊆ A) :
    ((G.graphicMatroid ／ prev) ↾ A).IsBase T ↔
      G.IsForest (I₀ ∪ T) ∧ ∀ e ∈ A \ T, ¬ G.IsForest (I₀ ∪ insert e T) := by
  have hI₀basis : G.graphicMatroid.IsBasis' I₀ prev := Matroid.isBase_restrict_iff'.mp hI₀
  have hI₀prev : I₀ ⊆ prev := hI₀basis.subset
  have hAprev : Disjoint A prev := by
    have h := hAE
    rw [Matroid.contract_ground] at h
    exact (Set.subset_sdiff.mp h).2
  have hindep_iff : ∀ S : Set E, S ⊆ A →
      (((G.graphicMatroid ／ prev) ↾ A).Indep S ↔ G.IsForest (I₀ ∪ S)) := by
    intro S hSA
    have hdisjPS : Disjoint prev S := hAprev.symm.mono_right hSA
    rw [Matroid.restrict_indep_iff, hI₀basis.contract_indep_iff, Multigraph.graphicMatroid_indep,
      and_iff_left hSA, and_iff_left hdisjPS, Set.union_comm]
  constructor
  · intro hbase
    have hindepT : G.IsForest (I₀ ∪ T) := (hindep_iff T hTA).mp hbase.indep
    refine ⟨hindepT, fun e he hforest => ?_⟩
    have heA : e ∈ A := he.1
    have heT : e ∉ T := he.2
    have hinsA : insert e T ⊆ A := Set.insert_subset heA hTA
    have hindepIns : ((G.graphicMatroid ／ prev) ↾ A).Indep (insert e T) :=
      (hindep_iff (insert e T) hinsA).mpr hforest
    have heqT : T = insert e T := hbase.eq_of_subset_indep hindepIns (Set.subset_insert e T)
    exact heT (heqT ▸ Set.mem_insert e T)
  · rintro ⟨hindepT, hmax⟩
    have hTindep : ((G.graphicMatroid ／ prev) ↾ A).Indep T := (hindep_iff T hTA).mpr hindepT
    refine hTindep.isBase_of_forall_insert (fun e he => ?_)
    rw [Matroid.restrict_ground_eq] at he
    have hindepIns_iff : ((G.graphicMatroid ／ prev) ↾ A).Indep (insert e T) ↔
        G.IsForest (I₀ ∪ insert e T) := hindep_iff (insert e T) (Set.insert_subset he.1 hTA)
    rw [hindepIns_iff]
    exact hmax e he

end DiscreteModulusCert
