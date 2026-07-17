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

/-- List-membership facts feeding `S_ne_of_mem_not_mem`/marginal computations
below, stated over arbitrary edges (not just concrete literals), since the
generic triangle-marginal lemma quantifies over which edges play which role. -/
theorem mem_fst (a b : E) : a ∈ ([a, b] : List E) := by simp

theorem mem_snd (a b : E) : b ∈ ([a, b] : List E) := by simp

theorem not_mem_two {a b x : E} (hxa : x ≠ a) (hxb : x ≠ b) : x ∉ ([a, b] : List E) := by
  simp [hxa, hxb]

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

/-! ## Generic marginal computation for a "triangle" local pmf

Both of `house`'s pieces have the same shape: three edges `a, b, c`, three
spanning trees of the block `{a,b}, {a,c}, {b,c}`, each at weight `1/3`.
Proved once, generically over the ambient matroid `M` and which of `a, b, c`
is being queried, and instantiated per-piece/per-edge below rather than
repeating the `Finset.sum_insert` bookkeeping six times. -/

private theorem trianglePmf_disjoint {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (S [a, b] : Set E) ≠ S [a, c] ∧ (S [a, b] : Set E) ≠ S [b, c] ∧
      (S [a, c] : Set E) ≠ S [b, c] :=
  ⟨S_ne_of_mem_not_mem (mem_snd a b) (not_mem_two hab.symm hbc),
    S_ne_of_mem_not_mem (mem_fst a b) (not_mem_two hab hac),
    S_ne_of_mem_not_mem (mem_fst a c) (not_mem_two hab hac)⟩

theorem trianglePmf_marginal_fst {M : Matroid E} (μ : Pmf M) {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupp : μ.support = {S [a, b], S [a, c], S [b, c]})
    (hwab : μ.weight (S [a, b]) = 1 / 3) (hwac : μ.weight (S [a, c]) = 1 / 3)
    (hwbc : μ.weight (S [b, c]) = 1 / 3) :
    μ.marginal a = 2 / 3 := by
  obtain ⟨hd1, hd2, hd3⟩ := trianglePmf_disjoint hab hac hbc
  have ha1 : (a : E) ∈ (S [a, b] : Set E) := by simp [S]
  have ha2 : (a : E) ∈ (S [a, c] : Set E) := by simp [S]
  have ha3 : (a : E) ∉ (S [b, c] : Set E) := by simp [S, hab, hac]
  show (∑ T ∈ μ.support, μ.weight T * usageVector T a) = 2 / 3
  rw [hsupp, show ({S [a, b], S [a, c], S [b, c]} : Finset (Set E)) =
    insert (S [a, b]) (insert (S [a, c]) {S [b, c]}) from rfl,
    Finset.sum_insert (by simp [hd1, hd2]), Finset.sum_insert (by simp [hd3]),
    Finset.sum_singleton]
  rw [usageVector_apply, if_pos ha1, usageVector_apply, if_pos ha2,
    usageVector_apply, if_neg ha3, hwab, hwac, hwbc]
  norm_num

theorem trianglePmf_marginal_mid {M : Matroid E} (μ : Pmf M) {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupp : μ.support = {S [a, b], S [a, c], S [b, c]})
    (hwab : μ.weight (S [a, b]) = 1 / 3) (hwac : μ.weight (S [a, c]) = 1 / 3)
    (hwbc : μ.weight (S [b, c]) = 1 / 3) :
    μ.marginal b = 2 / 3 := by
  obtain ⟨hd1, hd2, hd3⟩ := trianglePmf_disjoint hab hac hbc
  have hb1 : (b : E) ∈ (S [a, b] : Set E) := by simp [S]
  have hb2 : (b : E) ∉ (S [a, c] : Set E) := by simp [S, hab.symm, hbc]
  have hb3 : (b : E) ∈ (S [b, c] : Set E) := by simp [S]
  show (∑ T ∈ μ.support, μ.weight T * usageVector T b) = 2 / 3
  rw [hsupp, show ({S [a, b], S [a, c], S [b, c]} : Finset (Set E)) =
    insert (S [a, b]) (insert (S [a, c]) {S [b, c]}) from rfl,
    Finset.sum_insert (by simp [hd1, hd2]), Finset.sum_insert (by simp [hd3]),
    Finset.sum_singleton]
  rw [usageVector_apply, if_pos hb1, usageVector_apply, if_neg hb2,
    usageVector_apply, if_pos hb3, hwab, hwac, hwbc]
  norm_num

theorem trianglePmf_marginal_snd {M : Matroid E} (μ : Pmf M) {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupp : μ.support = {S [a, b], S [a, c], S [b, c]})
    (hwab : μ.weight (S [a, b]) = 1 / 3) (hwac : μ.weight (S [a, c]) = 1 / 3)
    (hwbc : μ.weight (S [b, c]) = 1 / 3) :
    μ.marginal c = 2 / 3 := by
  obtain ⟨hd1, hd2, hd3⟩ := trianglePmf_disjoint hab hac hbc
  have hc1 : (c : E) ∉ (S [a, b] : Set E) := by simp [S, hac.symm, hbc.symm]
  have hc2 : (c : E) ∈ (S [a, c] : Set E) := by simp [S]
  have hc3 : (c : E) ∈ (S [b, c] : Set E) := by simp [S]
  show (∑ T ∈ μ.support, μ.weight T * usageVector T c) = 2 / 3
  rw [hsupp, show ({S [a, b], S [a, c], S [b, c]} : Finset (Set E)) =
    insert (S [a, b]) (insert (S [a, c]) {S [b, c]}) from rfl,
    Finset.sum_insert (by simp [hd1, hd2]), Finset.sum_insert (by simp [hd3]),
    Finset.sum_singleton]
  rw [usageVector_apply, if_neg hc1, usageVector_apply, if_pos hc2,
    usageVector_apply, if_pos hc3, hwab, hwac, hwbc]
  norm_num

/-- An edge outside a triangle-shaped local pmf's own three edges has
marginal `0` -- every one of the three trees consists entirely of `{a,b,c}`
edges, so `usageVector` at `d` vanishes on all of them regardless of
weight. Used below to combine two pieces' local marginals into the
fully-glued pmf's marginal at edges outside a given piece. -/
theorem trianglePmf_marginal_zero {M : Matroid E} (μ : Pmf M) {a b c d : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hda : d ≠ a) (hdb : d ≠ b) (hdc : d ≠ c)
    (hsupp : μ.support = {S [a, b], S [a, c], S [b, c]}) :
    μ.marginal d = 0 := by
  obtain ⟨hd1, hd2, hd3⟩ := trianglePmf_disjoint hab hac hbc
  have hdab : (d : E) ∉ (S [a, b] : Set E) := by simp [S, hda, hdb]
  have hdac : (d : E) ∉ (S [a, c] : Set E) := by simp [S, hda, hdc]
  have hdbc : (d : E) ∉ (S [b, c] : Set E) := by simp [S, hdb, hdc]
  show (∑ T ∈ μ.support, μ.weight T * usageVector T d) = 0
  rw [hsupp, show ({S [a, b], S [a, c], S [b, c]} : Finset (Set E)) =
    insert (S [a, b]) (insert (S [a, c]) {S [b, c]}) from rfl,
    Finset.sum_insert (by simp [hd1, hd2]), Finset.sum_insert (by simp [hd3]),
    Finset.sum_singleton]
  rw [usageVector_apply, if_neg hdab, usageVector_apply, if_neg hdac,
    usageVector_apply, if_neg hdbc]
  ring

/-- `S` doesn't care about the order of a two-element edge list -- needed
because `piece2Pmf`'s support is literally written `{S[3,5], S[3,4], S[4,5]}`
(the order `certificate_builder` happened to emit trees in), which doesn't
match the canonical `{S[a,b], S[a,c], S[b,c]}` shape the generic lemmas
above are stated for without reordering one pair. -/
theorem S_comm (a b : E) : (S [a, b] : Set E) = S [b, a] := by
  ext x; simp only [S, Set.mem_setOf_eq, List.mem_cons]
  tauto

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
  pmf := piece1Pmf.cast (by rw [S_nil])

noncomputable def piece2 : Piece G.graphicMatroid (∅ ∪ S [0, 1, 2] : Set E) where
  A := S [3, 4, 5]
  hAE := by rw [Set.empty_union]; exact piece2_hAE
  pmf := piece2Pmf.cast (by rw [Set.empty_union])

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

/-! ## Extending the marginal spot-check to every edge, and to the
fully-glued `houseFullPmf`

`piece1Pmf_marginal_0` above hand-checks one edge against one piece's local
pmf. This section covers the remaining five edges (via the generic triangle
lemmas above) and then propagates all six through `Pmf.glue`'s
marginal-compositionality theorem to `houseFullPmf` itself, matching
`cpp/examples/house.eta`'s `eta* = 2/3` on every edge, not just edge `0`. -/

/-- `piece1Pmf`'s own weight at each of its three trees -- feeds both the
"2/3" marginal facts on `{0,1,2}` and (via `trianglePmf_marginal_zero`,
which doesn't need weights) is unused for the "0" facts on `{3,4,5}`. -/
theorem piece1Pmf_weight_01 : piece1Pmf.weight (S [0, 1]) = 1 / 3 := by
  simp only [piece1Pmf]; rw [if_pos trivial]

theorem piece1Pmf_weight_02 : piece1Pmf.weight (S [0, 2]) = 1 / 3 := by
  obtain ⟨hd1, _, _⟩ := trianglePmf_disjoint (a := (0 : E)) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)
  simp only [piece1Pmf]; rw [if_neg hd1.symm, if_pos trivial]

theorem piece1Pmf_weight_12 : piece1Pmf.weight (S [1, 2]) = 1 / 3 := by
  obtain ⟨_, hd2, hd3⟩ := trianglePmf_disjoint (a := (0 : E)) (b := 1) (c := 2)
    (by decide) (by decide) (by decide)
  simp only [piece1Pmf]; rw [if_neg hd2.symm, if_neg hd3.symm, if_pos trivial]

theorem piece1Pmf_marginal_1 : piece1Pmf.marginal 1 = 2 / 3 :=
  trianglePmf_marginal_mid piece1Pmf (a := 0) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) rfl
    piece1Pmf_weight_01 piece1Pmf_weight_02 piece1Pmf_weight_12

theorem piece1Pmf_marginal_2 : piece1Pmf.marginal 2 = 2 / 3 :=
  trianglePmf_marginal_snd piece1Pmf (a := 0) (b := 1) (c := 2)
    (by decide) (by decide) (by decide) rfl
    piece1Pmf_weight_01 piece1Pmf_weight_02 piece1Pmf_weight_12

theorem piece1Pmf_marginal_3 : piece1Pmf.marginal 3 = 0 :=
  trianglePmf_marginal_zero piece1Pmf (a := 0) (b := 1) (c := 2) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

theorem piece1Pmf_marginal_4 : piece1Pmf.marginal 4 = 0 :=
  trianglePmf_marginal_zero piece1Pmf (a := 0) (b := 1) (c := 2) (d := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

theorem piece1Pmf_marginal_5 : piece1Pmf.marginal 5 = 0 :=
  trianglePmf_marginal_zero piece1Pmf (a := 0) (b := 1) (c := 2) (d := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl

/-- `piece2Pmf`'s support, reordered via `S_comm` to match the generic
lemmas' canonical `{S[a,b], S[a,c], S[b,c]}` shape with `a := 3, b := 5,
c := 4` -- `certificate_builder` happened to emit this piece's trees in
`{3,5},{3,4},{4,5}` order, whereas the canonical shape needs the *third*
pair as `S[5,4]`, not `S[4,5]` (equal as sets, different edge-index lists). -/
theorem piece2Pmf_support_eq :
    piece2Pmf.support = ({S [3, 5], S [3, 4], S [5, 4]} : Finset (Set E)) := by
  show ({S [3, 5], S [3, 4], S [4, 5]} : Finset (Set E)) = {S [3, 5], S [3, 4], S [5, 4]}
  rw [S_comm 4 5]

theorem piece2Pmf_weight_35 : piece2Pmf.weight (S [3, 5]) = 1 / 3 := by
  simp only [piece2Pmf]; rw [if_pos trivial]

theorem piece2Pmf_weight_34 : piece2Pmf.weight (S [3, 4]) = 1 / 3 := by
  have hd : S ([3, 5] : List E) ≠ S [3, 4] :=
    S_ne_of_mem_not_mem (l₁ := [3, 5]) (x := 5) (by decide) (by decide)
  simp only [piece2Pmf]; rw [if_neg hd.symm, if_pos trivial]

theorem piece2Pmf_weight_45 : piece2Pmf.weight (S [4, 5]) = 1 / 3 := by
  have hd1 : S ([3, 5] : List E) ≠ S [4, 5] :=
    S_ne_of_mem_not_mem (l₁ := [3, 5]) (x := 3) (by decide) (by decide)
  have hd2 : S ([3, 4] : List E) ≠ S [4, 5] :=
    S_ne_of_mem_not_mem (l₁ := [3, 4]) (x := 3) (by decide) (by decide)
  simp only [piece2Pmf]; rw [if_neg hd1.symm, if_neg hd2.symm, if_pos trivial]

theorem piece2Pmf_weight_54 : piece2Pmf.weight (S [5, 4]) = 1 / 3 := by
  rw [← S_comm 4 5]; exact piece2Pmf_weight_45

theorem piece2Pmf_marginal_3 : piece2Pmf.marginal 3 = 2 / 3 :=
  trianglePmf_marginal_fst piece2Pmf (a := 3) (b := 5) (c := 4)
    (by decide) (by decide) (by decide) piece2Pmf_support_eq
    piece2Pmf_weight_35 piece2Pmf_weight_34 piece2Pmf_weight_54

theorem piece2Pmf_marginal_5 : piece2Pmf.marginal 5 = 2 / 3 :=
  trianglePmf_marginal_mid piece2Pmf (a := 3) (b := 5) (c := 4)
    (by decide) (by decide) (by decide) piece2Pmf_support_eq
    piece2Pmf_weight_35 piece2Pmf_weight_34 piece2Pmf_weight_54

theorem piece2Pmf_marginal_4 : piece2Pmf.marginal 4 = 2 / 3 :=
  trianglePmf_marginal_snd piece2Pmf (a := 3) (b := 5) (c := 4)
    (by decide) (by decide) (by decide) piece2Pmf_support_eq
    piece2Pmf_weight_35 piece2Pmf_weight_34 piece2Pmf_weight_54

theorem piece2Pmf_marginal_0 : piece2Pmf.marginal 0 = 0 :=
  trianglePmf_marginal_zero piece2Pmf (a := 3) (b := 5) (c := 4) (d := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) piece2Pmf_support_eq

theorem piece2Pmf_marginal_1 : piece2Pmf.marginal 1 = 0 :=
  trianglePmf_marginal_zero piece2Pmf (a := 3) (b := 5) (c := 4) (d := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) piece2Pmf_support_eq

theorem piece2Pmf_marginal_2 : piece2Pmf.marginal 2 = 0 :=
  trianglePmf_marginal_zero piece2Pmf (a := 3) (b := 5) (c := 4) (d := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) piece2Pmf_support_eq

/-- `piece1`/`piece2`'s own local pmfs (as `Piece` fields) are, by
construction (`Pmf.cast`), literally casts of `piece1Pmf`/`piece2Pmf` along
a matroid-level equality induced by `S_nil`/`Set.empty_union` -- so their
marginals agree with `piece1Pmf`/`piece2Pmf`'s directly via
`Pmf.cast_marginal`. -/
theorem piece1_pmf_marginal (e : E) : piece1.pmf.marginal e = piece1Pmf.marginal e := by
  unfold piece1; exact Pmf.cast_marginal _ piece1Pmf e

theorem piece2_pmf_marginal (e : E) : piece2.pmf.marginal e = piece2Pmf.marginal e := by
  unfold piece2; exact Pmf.cast_marginal _ piece2Pmf e

/-- `houseCertPieces`'s own `marginalSum` (the sum of its two pieces' local
marginals, `PieceList.marginalSum`'s recursive definition unfolded on this
concrete two-element list) reduces to the two local pmfs' own marginals. -/
theorem houseCertPieces_marginalSum (e : E) :
    houseCertPieces.marginalSum e = piece1Pmf.marginal e + piece2Pmf.marginal e := by
  show (0 + piece1.pmf.marginal e) + piece2.pmf.marginal e
    = piece1Pmf.marginal e + piece2Pmf.marginal e
  rw [piece1_pmf_marginal, piece2_pmf_marginal, zero_add]

/-- **`houseFullPmf`'s marginal, reduced to the two pieces' own local
marginals.** Goes through `PieceList.glueAllGraph`'s definition
(`Pmf.cast` composed with `PieceList.glueAll`), `Pmf.cast_marginal`,
`PieceList.glueAll_marginal` (the compositionality theorem,
`Glue.lean`), and `PieceList.marginalSum_cast` (transporting `marginalSum`
along the partition-completeness proof `houseCert_covers` doesn't change
it) -- never touching the exponentially-large glued support directly. -/
theorem houseFullPmf_marginal {e : E}
    (h : piece1Pmf.marginal e + piece2Pmf.marginal e = 2 / 3) :
    houseFullPmf.marginal e = 2 / 3 := by
  unfold houseFullPmf PieceList.glueAllGraph
  rw [Pmf.cast_marginal, PieceList.glueAll_marginal, PieceList.marginalSum_cast,
    houseCertPieces_marginalSum]
  exact h

/-- **The full spot-check**: every one of `examples/house`'s six edges has
marginal `2/3` under `houseFullPmf`, matching `cpp/examples/house.eta`
exactly -- not just edge `0` (`piece1Pmf_marginal_0`'s original, narrower
check), and now against the fully-glued kernel-checked pmf itself, not just
one piece's local pmf. -/
theorem houseFullPmf_marginal_0 : houseFullPmf.marginal 0 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_0, piece2Pmf_marginal_0]; norm_num)

theorem houseFullPmf_marginal_1 : houseFullPmf.marginal 1 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_1, piece2Pmf_marginal_1]; norm_num)

theorem houseFullPmf_marginal_2 : houseFullPmf.marginal 2 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_2, piece2Pmf_marginal_2]; norm_num)

theorem houseFullPmf_marginal_3 : houseFullPmf.marginal 3 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_3, piece2Pmf_marginal_3]; norm_num)

theorem houseFullPmf_marginal_4 : houseFullPmf.marginal 4 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_4, piece2Pmf_marginal_4]; norm_num)

theorem houseFullPmf_marginal_5 : houseFullPmf.marginal 5 = 2 / 3 :=
  houseFullPmf_marginal (by rw [piece1Pmf_marginal_5, piece2Pmf_marginal_5]; norm_num)

end HouseCert
end DiscreteModulusCert
