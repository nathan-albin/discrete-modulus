import DiscreteModulusCert.IsBaseCheck
import DiscreteModulusCert.ForestDecide
import DiscreteModulusCert.Glue
import Mathlib.Tactic.NormNum.Basic

/-!
# End-to-end verification of `examples/house`'s real certificate

First concrete instance of PR 5 (`Certification_Plan.md` §4 Phase C): takes
the exact data `certificate_builder.build_certificate` produced for
`examples/house` (5 vertices, 6 edges, 2 pieces of 3 edges/3 trees each,
`cpp/examples/house.eta`'s known `eta* = 2/3` on every edge) and checks it
entirely inside Lean, using the already-proved machinery
(`isBase_contract_restrict_iff_isForest`, `instDecidableIsForestOfList`,
`PieceList`/`Pmf.glue`), with no hand-written proof terms for the
individual forest/maximality/weight checks -- those are all discharged by
`decide`/`native_decide` against the certificate's own concrete data.

This is deliberately hand-transcribed (not yet parsed from the actual JSON
file) to validate the whole per-piece-verification-then-gluing pipeline on
real data before investing in a JSON parser or a Python-side codegen step
-- see the module docstring's closing note for what's still open.
-/

namespace DiscreteModulusCert
namespace HouseCert

open scoped Matroid
open Multigraph Classical

/-- 5 vertices, matching `cpp/examples/house.edges`. -/
abbrev V := Fin 5

/-- 6 edges, indexed exactly as `certificate_builder`'s `graph.edges` array
(global edge index = array position). -/
abbrev E := Fin 6

/-- The endpoints of each edge, transcribed directly from the certificate's
`"graph": {"edges": [[0,1],[0,4],[1,4],[1,2],[2,3],[3,4]]}`. -/
def houseEndpoints : E → V × V
  | 0 => (0, 1)
  | 1 => (0, 4)
  | 2 => (1, 4)
  | 3 => (1, 2)
  | 4 => (2, 3)
  | 5 => (3, 4)

def G : Multigraph V E := ⟨fun e => s((houseEndpoints e).1, (houseEndpoints e).2)⟩

/-- The edge set of an edge-index list, in exactly the `{e | e ∈ l}` shape
`instDecidableIsForestOfList` is stated for. `abbrev`, not `def`: instance
search for `Decidable (G.IsForest (S l))` needs to see through this to the
literal `{e | e ∈ l}` shape the instance is stated for. -/
abbrev S (l : List E) : Set E := {e | e ∈ l}

/-- Two edge-index lists denote different edge sets whenever some edge is
in one but not the other -- avoids ever needing `Set E`'s (classically,
noncomputably) decidable equality, unlike `native_decide` on `S l₁ ≠ S l₂`
directly. -/
theorem S_ne_of_mem_not_mem {l₁ l₂ : List E} {x : E} (hx1 : x ∈ l₁) (hx2 : x ∉ l₂) :
    S l₁ ≠ S l₂ := by
  intro h
  apply hx2
  have hx1' : x ∈ S l₁ := hx1
  rw [h] at hx1'
  exact hx1'

/-- Subset of edge-index lists lifts to subset of their `S`-denoted edge
sets -- computable/`decide`-friendly on the list side, unlike `Set.Subset`
directly. -/
theorem S_subset_of_forall_mem {l₁ l₂ : List E} (h : ∀ x ∈ l₁, x ∈ l₂) :
    S l₁ ⊆ S l₂ := h

theorem S_append (l₁ l₂ : List E) : S l₁ ∪ S l₂ = S (l₁ ++ l₂) := by
  ext x; simp [S, List.mem_append]

theorem S_cons (a : E) (l : List E) : insert a (S l) = S (a :: l) := by
  ext x; simp [S, List.mem_cons]

theorem S_nil : S ([] : List E) = (∅ : Set E) := by ext x; simp [S]

/-- The forest-check half of `isBase_contract_restrict_iff_isForest`,
rephrased so `native_decide`/`decide` sees a literal `S l`-shaped forest
check (matching `instDecidableIsForestOfList`'s exact statement) instead of
a `Set`-level union that instance search can't see through. -/
theorem isForest_S_union (I₀ T : List E) :
    G.IsForest (S I₀ ∪ S T) ↔ G.IsForest (S (I₀ ++ T)) := by rw [S_append]

/-- The maximality-check half: lifts a `List`-quantified, `decide`-friendly
check (never naming `Set.diff`/`Set`-level membership, which routes
through classical, non-computable decidability, nor `Set.insert`, which
instance search can't see through to a literal `S l` shape) to the
`Set`-level statement `isBase_contract_restrict_iff_isForest`'s maximality
clause needs. -/
theorem forall_diff_not_isForest_of_list_all {I₀ A T : List E}
    (h : ∀ e ∈ A, e ∉ T → ¬ G.IsForest (S (e :: (I₀ ++ T)))) :
    ∀ e ∈ S A \ S T, ¬ G.IsForest (S I₀ ∪ insert e (S T)) := by
  intro e he
  have heq : S I₀ ∪ insert e (S T) = S (e :: (I₀ ++ T)) := by
    ext x
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, List.mem_cons,
      List.mem_append]
    tauto
  rw [heq]
  exact h e he.1 he.2

/-! ## Piece 1: edges `{0, 1, 2}` (the chord triangle on vertices `{0, 1, 4}`),
`prev = ∅`. Trees `{0,1}, {0,2}, {1,2}`, each weight `1/3` -- transcribed
directly from `certificate_builder`'s output for `examples/house`. -/

theorem piece1_hI₀ : (G.graphicMatroid ↾ (S [] : Set E)).IsBase (S ([] : List E)) := by
  rw [S_nil]
  exact (trivialPmf G.graphicMatroid).isBase ∅ (Finset.mem_singleton_self ∅)

theorem piece1_hAE : S [0, 1, 2] ⊆ (G.graphicMatroid ／ S ([] : List E)).E := by
  rw [Matroid.contract_ground, S_nil, Multigraph.graphicMatroid_E, Set.sdiff_empty]
  exact Set.subset_univ _

theorem piece1_isBase_01 : ((G.graphicMatroid ／ S ([] : List E)) ↾ S [0, 1, 2]).IsBase (S [0, 1]) := by
  rw [isBase_contract_restrict_iff_isForest G piece1_hI₀ piece1_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [] [0, 1]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := []) (by native_decide)⟩

theorem piece1_isBase_02 : ((G.graphicMatroid ／ S ([] : List E)) ↾ S [0, 1, 2]).IsBase (S [0, 2]) := by
  rw [isBase_contract_restrict_iff_isForest G piece1_hI₀ piece1_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [] [0, 2]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := []) (by native_decide)⟩

theorem piece1_isBase_12 : ((G.graphicMatroid ／ S ([] : List E)) ↾ S [0, 1, 2]).IsBase (S [1, 2]) := by
  rw [isBase_contract_restrict_iff_isForest G piece1_hI₀ piece1_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [] [1, 2]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := []) (by native_decide)⟩

/-! ## Piece 2: edges `{3, 4, 5}` (the triangle on `{__core_0__, 2, 3}` after
contracting piece 1's chord triangle), `prev = {0, 1, 2}`. Trees
`{3,5}, {3,4}, {4,5}`, each weight `1/3` -- transcribed directly from
`certificate_builder`'s output. Needs an already-verified representative
spanning tree of `prev` (`piece1_isBase_01`'s own witness, `{0,1}`) to run
`isBase_contract_restrict_iff_isForest` against -- any one of piece 1's own
trees works equally well, by the matroid theory `isBase_contract_iff_of_isBasis_restrict`
(`Glue.lean`) already establishes. -/

theorem piece2_hI₀ : (G.graphicMatroid ↾ (S [0, 1, 2] : Set E)).IsBase (S [0, 1]) := by
  have h := piece1_isBase_01
  rwa [S_nil, Matroid.contract_empty] at h

theorem piece2_hAE : S [3, 4, 5] ⊆ (G.graphicMatroid ／ S [0, 1, 2]).E := by
  rw [Matroid.contract_ground, Multigraph.graphicMatroid_E]
  intro x hx
  exact ⟨Set.mem_univ x, by revert x; decide⟩

theorem piece2_isBase_35 :
    ((G.graphicMatroid ／ S [0, 1, 2]) ↾ S [3, 4, 5]).IsBase (S [3, 5]) := by
  rw [isBase_contract_restrict_iff_isForest G piece2_hI₀ piece2_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [0, 1] [3, 5]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := [0, 1]) (by native_decide)⟩

theorem piece2_isBase_34 :
    ((G.graphicMatroid ／ S [0, 1, 2]) ↾ S [3, 4, 5]).IsBase (S [3, 4]) := by
  rw [isBase_contract_restrict_iff_isForest G piece2_hI₀ piece2_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [0, 1] [3, 4]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := [0, 1]) (by native_decide)⟩

theorem piece2_isBase_45 :
    ((G.graphicMatroid ／ S [0, 1, 2]) ↾ S [3, 4, 5]).IsBase (S [4, 5]) := by
  rw [isBase_contract_restrict_iff_isForest G piece2_hI₀ piece2_hAE
    (S_subset_of_forall_mem (by decide))]
  exact ⟨(isForest_S_union [0, 1] [4, 5]).mpr (by native_decide),
    forall_diff_not_isForest_of_list_all (I₀ := [0, 1]) (by native_decide)⟩

noncomputable def piece2Pmf : Pmf ((G.graphicMatroid ／ S [0, 1, 2]) ↾ S [3, 4, 5]) where
  support := {S [3, 5], S [3, 4], S [4, 5]}
  weight := fun T => if T = S [3, 5] then (1 : ℚ) / 3
    else if T = S [3, 4] then (1 : ℚ) / 3
    else if T = S [4, 5] then (1 : ℚ) / 3
    else 0
  isBase := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with h | h | h <;> subst h
    · exact piece2_isBase_35
    · exact piece2_isBase_34
    · exact piece2_isBase_45
  nonneg := by
    intro T _
    split_ifs with h1 h2 h3
    · exact by native_decide
    · exact by native_decide
    · exact by native_decide
    · exact le_refl 0
  sum_one := by
    have hd01 : S ([3, 5] : List E) ≠ S [3, 4] := S_ne_of_mem_not_mem (l₁ := [3, 5]) (x := 5)
      (by decide) (by decide)
    have hd02 : S ([3, 5] : List E) ≠ S [4, 5] := S_ne_of_mem_not_mem (l₁ := [3, 5]) (x := 3)
      (by decide) (by decide)
    have hd12 : S ([3, 4] : List E) ≠ S [4, 5] := S_ne_of_mem_not_mem (l₁ := [3, 4]) (x := 3)
      (by decide) (by decide)
    rw [show ({S [3, 5], S [3, 4], S [4, 5]} : Finset (Set E)) =
      insert (S [3, 5]) (insert (S [3, 4]) {S [4, 5]}) from rfl]
    rw [Finset.sum_insert (by simp [hd01, hd02]), Finset.sum_insert (by simp [hd12]),
      Finset.sum_singleton]
    rw [if_pos rfl, if_neg hd01.symm, if_pos rfl, if_neg hd02.symm, if_neg hd12.symm, if_pos rfl]
    norm_num

noncomputable def piece1Pmf : Pmf ((G.graphicMatroid ／ S ([] : List E)) ↾ S [0, 1, 2]) where
  support := {S [0, 1], S [0, 2], S [1, 2]}
  weight := fun T => if T = S [0, 1] then (1 : ℚ) / 3
    else if T = S [0, 2] then (1 : ℚ) / 3
    else if T = S [1, 2] then (1 : ℚ) / 3
    else 0
  isBase := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with h | h | h <;> subst h
    · exact piece1_isBase_01
    · exact piece1_isBase_02
    · exact piece1_isBase_12
  nonneg := by
    intro T _
    split_ifs with h1 h2 h3
    · exact by native_decide
    · exact by native_decide
    · exact by native_decide
    · exact le_refl 0
  sum_one := by
    have hd01 : S ([0, 1] : List E) ≠ S [0, 2] := S_ne_of_mem_not_mem (l₁ := [0, 1]) (x := 1)
      (by decide) (by decide)
    have hd02 : S ([0, 1] : List E) ≠ S [1, 2] := S_ne_of_mem_not_mem (l₁ := [0, 1]) (x := 0)
      (by decide) (by decide)
    have hd12 : S ([0, 2] : List E) ≠ S [1, 2] := S_ne_of_mem_not_mem (l₁ := [0, 2]) (x := 0)
      (by decide) (by decide)
    rw [show ({S [0, 1], S [0, 2], S [1, 2]} : Finset (Set E)) =
      insert (S [0, 1]) (insert (S [0, 2]) {S [1, 2]}) from rfl]
    rw [Finset.sum_insert (by simp [hd01, hd02]), Finset.sum_insert (by simp [hd12]),
      Finset.sum_singleton]
    rw [if_pos rfl, if_neg hd01.symm, if_pos rfl, if_neg hd02.symm, if_neg hd12.symm, if_pos rfl]
    norm_num

/-! ## Assembly: fold both pieces, glue, and check the result is a genuine
pmf on all of `G`'s spanning trees. -/

noncomputable def piece1 : Piece G.graphicMatroid (∅ : Set E) where
  A := S [0, 1, 2]
  hAE := by rw [← S_nil]; exact piece1_hAE
  pmf := by rw [← S_nil]; exact piece1Pmf

noncomputable def piece2 : Piece G.graphicMatroid (∅ ∪ S [0, 1, 2] : Set E) where
  A := S [3, 4, 5]
  hAE := by rw [Set.empty_union]; exact piece2_hAE
  pmf := by rw [Set.empty_union]; exact piece2Pmf

/-- The certificate's two pieces, folded into one flat `PieceList` -- exactly
`certificate_builder.build_certificate`'s own `pieces` array, in order. -/
noncomputable def houseCertPieces :
    PieceList G.graphicMatroid (∅ ∪ S [0, 1, 2] ∪ S [3, 4, 5]) :=
  PieceList.cons (PieceList.cons PieceList.nil piece1) piece2

/-- Partition-completeness: the certificate's pieces cover every one of
`examples/house`'s 6 edges -- checked here exactly as `validate_certificate`
(the untrusted Python-side check) does, but now inside the kernel. -/
theorem houseCert_covers : (∅ ∪ S [0, 1, 2] ∪ S [3, 4, 5] : Set E) = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  simp only [Set.mem_union, Set.mem_empty_iff_false, false_or]
  revert x
  decide

/-- **The certificate accepted**: `examples/house`'s two pieces glue into a
genuine `Pmf` on all of `G.graphicMatroid`'s bases -- i.e. a valid,
exact-rational probability distribution on spanning trees of `G`, entirely
checked by the kernel from the certificate's own concrete data (no
hand-written per-tree proof terms; every forest/maximality/weight fact
discharged by `decide`/`native_decide`). -/
noncomputable def houseFullPmf : Pmf G.graphicMatroid :=
  PieceList.glueAllGraph (Multigraph.graphicMatroid_E G) (houseCert_covers ▸ houseCertPieces)

/-- **Spot-check against the known answer**: `cpp/examples/house.eta`
records `eta* = 2/3` on every edge; edge `0` sits in piece 1, where two of
the three trees (`{0,1}`, `{0,2}`) use it and one (`{1,2}`) doesn't, giving
exactly `1/3 + 1/3 = 2/3` -- computed here from the certificate's own local
pmf, independently of the Python builder that produced it. -/
theorem piece1Pmf_marginal_0 : piece1Pmf.marginal 0 = 2 / 3 := by
  have hd01 : S ([0, 1] : List E) ≠ S [0, 2] := S_ne_of_mem_not_mem (l₁ := [0, 1]) (x := 1)
    (by decide) (by decide)
  have hd02 : S ([0, 1] : List E) ≠ S [1, 2] := S_ne_of_mem_not_mem (l₁ := [0, 1]) (x := 0)
    (by decide) (by decide)
  have hd12 : S ([0, 2] : List E) ≠ S [1, 2] := S_ne_of_mem_not_mem (l₁ := [0, 2]) (x := 0)
    (by decide) (by decide)
  have h0 : (0 : E) ∈ (S [0, 1] : Set E) := by simp [S]
  have h0' : (0 : E) ∈ (S [0, 2] : Set E) := by simp [S]
  have h0'' : (0 : E) ∉ (S [1, 2] : Set E) := by simp [S]
  show (∑ T ∈ ({S [0, 1], S [0, 2], S [1, 2]} : Finset (Set E)),
    piece1Pmf.weight T * usageVector T 0) = 2 / 3
  rw [show ({S [0, 1], S [0, 2], S [1, 2]} : Finset (Set E)) =
    insert (S [0, 1]) (insert (S [0, 2]) {S [1, 2]}) from rfl]
  rw [Finset.sum_insert (by simp [hd01, hd02]), Finset.sum_insert (by simp [hd12]),
    Finset.sum_singleton]
  show (piece1Pmf.weight (S [0,1]) * usageVector (S [0,1]) 0
    + (piece1Pmf.weight (S [0,2]) * usageVector (S [0,2]) 0
      + piece1Pmf.weight (S [1,2]) * usageVector (S [1,2]) 0)) = 2 / 3
  simp only [piece1Pmf]
  rw [if_pos trivial, if_neg hd01.symm, if_pos trivial, if_neg hd02.symm, if_neg hd12.symm,
    if_pos trivial, usageVector_apply, if_pos h0, usageVector_apply, if_pos h0',
    usageVector_apply, if_neg h0'']
  norm_num

end HouseCert
end DiscreteModulusCert
