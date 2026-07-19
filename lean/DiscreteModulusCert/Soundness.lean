import DiscreteModulusCert.CertChecker
import DiscreteModulusCert.IsBaseCheck
import DiscreteModulusCert.Glue
import DiscreteModulusCert.Admissibility
import DiscreteModulusCert.Optimality
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The generic checker-to-proof-term soundness theorem

`CertChecker.lean`'s `checkCertificate` is an ordinary executable function
(`Except String Unit`) -- accepting a certificate is a runtime fact, not (by
itself) a kernel-checked proof that a genuine `Pmf`/`PieceList` exists for
that data. This file closes that gap generically, for *any* raw
certificate, not just `HouseCert.lean`'s hand-transcribed `house` instance:
`checkCertificate_sound` shows accepting implies a real `Pmf
G.graphicMatroid` and admissible `ρ` exist with `certificate_optimality`'s
conclusion.

Does not modify `CertChecker.lean` -- every theorem here is *about* its
existing, already-tested functions.
-/

namespace DiscreteModulusCert
namespace CertChecker

open scoped Matroid
open Multigraph

section MonadHelpers

variable {α β : Type*}

theorem check_eq_ok_iff {cond : Bool} {msg : String} :
    check cond msg = Except.ok PUnit.unit ↔ cond = true := by
  cases cond <;> simp [check]

/-- A successful `List.mapM` (over `Except String`) means `f` succeeded on
every input element, producing the corresponding output element -- used to
extract per-edge/per-tree facts from `checkPiece`'s two `mapM` calls
(`raw.edges.mapM toE`, and the per-tree conversion). -/
theorem mapM_ok_forall₂ {α β : Type*} (f : α → Except String β) :
    ∀ {l : List α} {r : List β}, l.mapM f = Except.ok r →
      List.Forall₂ (fun a b => f a = Except.ok b) l r
  | [], r, h => by
      simp only [List.mapM_nil] at h
      cases h
      exact List.Forall₂.nil
  | a :: t, r, h => by
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | error e =>
        rw [hfa] at h
        simp [bind, pure, Except.pure, Except.bind, Functor.map, Except.map] at h
      | ok b =>
        rw [hfa] at h
        cases htr : t.mapM f with
        | error e =>
          rw [htr] at h
          simp [bind, pure, Except.pure, Except.bind, Functor.map, Except.map] at h
        | ok bs =>
          rw [htr] at h
          simp only [bind, pure, Except.pure, Except.bind, Functor.map, Except.map,
            Except.ok.injEq] at h
          subst h
          exact List.Forall₂.cons hfa (mapM_ok_forall₂ f htr)

end MonadHelpers

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

/-! ## Generic `S`-manipulation lemmas

Ported from `HouseCert.lean`'s versions of the same facts, generalized from
that file's fixed concrete `house` graph to an arbitrary `V`/`E`/`G` -- none
of these actually depend on `G` except `forall_diff_not_isForest_of_list_all`. -/

theorem S_ne_of_mem_not_mem {l₁ l₂ : List E} {x : E} (hx1 : x ∈ l₁) (hx2 : x ∉ l₂) :
    (S l₁ : Set E) ≠ S l₂ := by
  intro h; apply hx2; have hx1' : x ∈ S l₁ := hx1; rw [h] at hx1'; exact hx1'

theorem S_subset_of_forall_mem {l₁ l₂ : List E} (h : ∀ x ∈ l₁, x ∈ l₂) : S l₁ ⊆ S l₂ := h

theorem S_append (l₁ l₂ : List E) : (S l₁ : Set E) ∪ S l₂ = S (l₁ ++ l₂) := by
  ext x; simp [S, List.mem_append]

/-- The list-level version of `isBase_contract_restrict_iff_isForest`'s
maximality conjunct, lifted to the `Set`-level statement that theorem
actually needs. -/
theorem forall_diff_not_isForest_of_list_all {G : Multigraph V E} {I₀ A T : List E}
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

/-- Connects a `Fin l.length`-indexed sum to the underlying list's sum --
independent of whether `f ∘ l.get` has repeated values, unlike a
`Finset`-image-based grouping would be. Used to build a `Pmf`'s `weight`
function by grouping declared trees by their *denoted edge set* without
needing to assume the certificate's raw tree list has no duplicate entries. -/
theorem sum_fin_length_eq_list_sum {α β : Type*} [AddCommMonoid β] (f : α → β) (l : List α) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [Fin.sum_univ_def, show (fun i => f (l.get i)) = f ∘ l.get from rfl, ← List.map_map,
    List.map_get_finRange]

open Classical in
/-- Builds a genuine `Pmf M` from a raw list of (edge-list, weight) pairs,
each independently known to denote a base of `M` -- grouping by *denoted
edge set* (`Fin trees.length`-indexed, so it needs no assumption that the
raw list has no duplicate entries) rather than assuming the list is already
deduplicated. This is the shape a certificate's own `local_pmf.trees` list
comes in. -/
noncomputable def treesPmf {M : Matroid E} {trees : List (List E × ℚ)}
    (hbase : ∀ t ∈ trees, M.IsBase (S t.1)) (hnonneg : ∀ t ∈ trees, 0 ≤ t.2)
    (hsum : (trees.map Prod.snd).sum = 1) : Pmf M where
  support := (Finset.univ : Finset (Fin trees.length)).image (fun i => S (trees.get i).1)
  weight := fun T => ∑ i ∈ (Finset.univ : Finset (Fin trees.length)).filter
    (fun i => S (trees.get i).1 = T), (trees.get i).2
  isBase := by
    intro T hT
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hT
    exact hi ▸ hbase (trees.get i) (List.get_mem trees i)
  nonneg := by
    intro T _
    exact Finset.sum_nonneg (fun i _ => hnonneg (trees.get i) (List.get_mem trees i))
  sum_one := by
    have hkey :
        (∑ T ∈ (Finset.univ : Finset (Fin trees.length)).image (fun i => S (trees.get i).1),
          ∑ i ∈ (Finset.univ : Finset (Fin trees.length)).filter
            (fun i => S (trees.get i).1 = T), (trees.get i).2)
          = ∑ i : Fin trees.length, (trees.get i).2 :=
      Finset.sum_image' (s := (Finset.univ : Finset (Fin trees.length)))
        (g := fun i => S (trees.get i).1)
        (f := fun T => ∑ i ∈ (Finset.univ : Finset (Fin trees.length)).filter
          (fun i => S (trees.get i).1 = T), (trees.get i).2)
        (fun i : Fin trees.length => (trees.get i).2) (fun i _ => rfl)
    rw [hkey, sum_fin_length_eq_list_sum Prod.snd trees]
    exact hsum

open Classical in
/-- **`treesPmf`'s marginal, in closed form** -- the per-edge sum
`CertChecker.sumTreeContributions` computes directly over the raw
`trees` list. Needed to show the constructed piece pmf's marginal matches
what the runtime checker already verified equals the certificate's declared
`eta`. -/
theorem treesPmf_marginal {M : Matroid E} {trees : List (List E × ℚ)}
    (hbase : ∀ t ∈ trees, M.IsBase (S t.1)) (hnonneg : ∀ t ∈ trees, 0 ≤ t.2)
    (hsum : (trees.map Prod.snd).sum = 1) (e : E) :
    (treesPmf hbase hnonneg hsum).marginal e =
      (trees.map (fun t => if e ∈ S t.1 then t.2 else 0)).sum := by
  have hstep1 :
      (treesPmf hbase hnonneg hsum).marginal e =
        ∑ T ∈ (Finset.univ : Finset (Fin trees.length)).image (fun i => S (trees.get i).1),
          ∑ i ∈ (Finset.univ : Finset (Fin trees.length)).filter
            (fun i => S (trees.get i).1 = T), (trees.get i).2 * usageVector (S (trees.get i).1) e := by
    show (∑ T ∈ _, (∑ i ∈ (Finset.univ : Finset (Fin trees.length)).filter
      (fun i => S (trees.get i).1 = T), (trees.get i).2) * usageVector T e) = _
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2])
  rw [hstep1,
    Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
  rw [show (fun i : Fin trees.length => (trees.get i).2 * usageVector (S (trees.get i).1) e)
      = (fun i : Fin trees.length => (fun t : List E × ℚ => if e ∈ S t.1 then t.2 else 0)
        (trees.get i)) from funext (fun i => by simp [usageVector_apply, mul_comm])]
  exact sum_fin_length_eq_list_sum (fun t => if e ∈ S t.1 then t.2 else 0) trees

/-- **Soundness of `checkTree`**: if it accepts, the declared tree really is
a base of the piece's own (contract-then-restrict) matroid -- the executable
mirror of `isBase_contract_restrict_iff_isForest`. -/
theorem checkTree_sound {G : Multigraph V E} {prev A I₀acc T : List E}
    (hI₀ : (G.graphicMatroid ↾ (S prev)).IsBase (S I₀acc))
    (hAE : S A ⊆ (G.graphicMatroid ／ (S prev)).E)
    (hok : checkTree G I₀acc A T = Except.ok PUnit.unit) :
    ((G.graphicMatroid ／ (S prev)) ↾ S A).IsBase (S T) := by
  unfold checkTree at hok
  simp only [check] at hok
  split_ifs at hok with h1 h2 <;> simp only [bind, Except.bind] at hok
  all_goals (try exact absurd hok (by simp))
  have hTA : T ⊆ A := by
    have := List.all_eq_true.mp h2
    intro e he; simpa using this e he
  rw [isBase_contract_restrict_iff_isForest G hI₀ hAE (S_subset_of_forall_mem hTA)]
  split at hok
  next hd => exact absurd hok (by simp)
  next hd =>
    have hforest : G.IsForest (S (I₀acc ++ T)) := of_decide_eq_true hd
    refine ⟨(S_append I₀acc T) ▸ hforest, ?_⟩
    split_ifs at hok with hmaxcond
    have hmax := List.all_eq_true.mp hmaxcond
    refine forall_diff_not_isForest_of_list_all (I₀ := I₀acc) (A := A) (T := T) (fun e heA heT => ?_)
    have he : e ∈ A.filter (· ∉ T) := List.mem_filter.mpr ⟨heA, by simpa using heT⟩
    have hthis := hmax e he
    have heq : S (e :: (I₀acc ++ T)) = {e_1 | e_1 = e ∨ e_1 ∈ I₀acc ∨ e_1 ∈ T} := by
      ext x; simp [S, List.mem_cons, List.mem_append]
    rw [heq]
    simpa using hthis

theorem subset_contract_E_of_disjoint {G : Multigraph V E} {prev A : List E}
    (hdisj : ∀ e ∈ A, e ∉ prev) :
    S A ⊆ (G.graphicMatroid ／ (S prev)).E := by
  rw [Matroid.contract_ground, graphicMatroid_E]
  refine Set.subset_diff.mpr ⟨Set.subset_univ _, ?_⟩
  rw [Set.disjoint_left]
  intro e he hep
  exact hdisj e he hep

/-- Threading a representative base of `prev` through one more block: if
`I₀` is a base of `N ↾ prev` and `T` is a base of the next block's own
(already-contracted) matroid `(N ／ prev) ↾ A`, then `I₀ ∪ T` is a base of
`N ↾ (prev ∪ A)` -- the fact that lets `checkPiece_sound` hand off a new
representative base to the next piece in the fold. Same restrict/contract
identities `PieceList.glueAll`'s `cons` case uses internally for whole
`Pmf`s, specialized here to a single base. -/
theorem isBase_restrict_union {N : Matroid E} {prev A : Set E} (hAE : A ⊆ (N ／ prev).E)
    {I₀ T : Set E} (hI₀ : (N ↾ prev).IsBase I₀) (hT : ((N ／ prev) ↾ A).IsBase T) :
    (N ↾ (prev ∪ A)).IsBase (I₀ ∪ T) := by
  have hdisjAU : Disjoint A prev := by
    have h := hAE
    rw [Matroid.contract_ground] at h
    exact (Set.subset_diff.mp h).2
  have hUsub : prev ⊆ (N ↾ (prev ∪ A)).E := by
    rw [Matroid.restrict_ground_eq]; exact Set.subset_union_left
  have heqRestrict : (N ↾ (prev ∪ A)) ↾ prev = N ↾ prev :=
    Matroid.restrict_restrict_eq N Set.subset_union_left
  have heqContract : (N ↾ (prev ∪ A)) ／ prev = (N ／ prev) ↾ A := by
    rw [Matroid.restrict_contract_eq_contract_restrict _ Set.subset_union_left]
    congr 1
    rw [Set.union_sdiff_left, sdiff_eq_left.mpr hdisjAU]
  have hI₀' : ((N ↾ (prev ∪ A)) ↾ prev).IsBase I₀ := heqRestrict ▸ hI₀
  have hT' : ((N ↾ (prev ∪ A)) ／ prev).IsBase T := heqContract ▸ hT
  have hTA : T ⊆ A := by
    have h := hT.subset_ground
    rwa [Matroid.restrict_ground_eq] at h
  have hTdisj : Disjoint T prev := Disjoint.mono_left hTA hdisjAU
  have hT'' : ((N ↾ (prev ∪ A)) ／ I₀).IsBase T :=
    (isBase_contract_iff_of_isBasis_restrict hUsub hI₀' hTdisj).mp hT'
  have hkey := isBase_union_of_isBase_restrict_isBase_contract hUsub hI₀' hT''
  rw [Set.union_comm I₀ T]
  exact hkey

theorem forall₂_right_of_forall₂_const {α β : Type*} {P : β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ (fun _ b => P b) l1 l2 → ∀ b ∈ l2, P b
  | _, _, List.Forall₂.nil, b, hb => absurd hb List.not_mem_nil
  | _, _, List.Forall₂.cons h ht, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact h
      · exact forall₂_right_of_forall₂_const ht b hb'

open Classical in
noncomputable def checkPiece_sound {G : Multigraph V E} {Uacc I₀acc : List E} {raw : RawPiece}
    {toE : Nat → Except String E} {A I₀acc' : List E}
    (hI₀ : (G.graphicMatroid ↾ (S Uacc)).IsBase (S I₀acc))
    (hok : checkPiece G Uacc I₀acc raw toE = Except.ok (A, I₀acc')) :
    Σ' (p : Piece G.graphicMatroid (S Uacc)),
      p.A = S A ∧ (G.graphicMatroid ↾ (S (Uacc ++ A))).IsBase (S I₀acc') ∧
      A.Nodup ∧ ∀ e ∈ A, e ∉ Uacc := by
  unfold checkPiece at hok
  simp only [check] at hok
  cases hA' : raw.edges.mapM toE with
  | error e =>
    rw [hA'] at hok
    simp [bind, pure, Except.pure, Except.bind, Functor.map, Except.map] at hok
  | ok A' =>
    rw [hA'] at hok
    simp only [bind, Except.bind] at hok
    split_ifs at hok with h1 h2 <;>
      simp only [bind, pure, Except.pure, Except.bind, Functor.map, Except.map] at hok
    all_goals (try (exfalso; simp at hok; done))
    have hA1 : A'.Nodup := of_decide_eq_true h1
    have hA2 : ∀ e ∈ A', e ∉ Uacc := by
      have := List.all_eq_true.mp h2
      intro e he; simpa using this e he
    split at hok
    next => exact absurd hok (by simp)
    next htrees =>
      rename_i trees
      split at hok
      next => exact absurd hok (by simp)
      next hhead =>
        rename_i T0 w0
        split at hok
        next => exact absurd hok (by simp)
        next hnn =>
          split at hok
          next => exact absurd hok (by simp)
          next hsum =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hok
            obtain ⟨hAeq, hI'eq⟩ := hok
            have hnncond : (trees.all fun t => decide (0 ≤ t.2)) = true := by
              by_contra hc
              rw [if_neg hc] at hnn
              exact absurd hnn (by simp)
            have hsumcond : (List.map Prod.snd trees).sum = 1 := by
              by_contra hc
              rw [if_neg (by simpa using hc)] at hsum
              exact absurd hsum (by simp)
            have hnonneg' : ∀ t ∈ trees, 0 ≤ t.2 := by
              have := List.all_eq_true.mp hnncond
              intro t ht; simpa using this t ht
            have hAE : S A' ⊆ (G.graphicMatroid ／ S Uacc).E := subset_contract_E_of_disjoint hA2
            have hbase_forall2 : List.Forall₂ (fun (_ : RawTree) (pair : List E × ℚ) =>
                ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S pair.1)) raw.local_pmf.trees trees := by
              refine (mapM_ok_forall₂ _ htrees).imp (fun rawT pair hpair => ?_)
              split at hpair
              next => exact absurd hpair (by simp)
              next hmapedges =>
                split at hpair
                next => exact absurd hpair (by simp)
                next hwcheck =>
                  split at hpair
                  next => exact absurd hpair (by simp)
                  next hct =>
                    simp only [Except.ok.injEq] at hpair
                    subst hpair
                    exact checkTree_sound hI₀ hAE hct
            have hbase : ∀ t ∈ trees, ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S t.1) :=
              forall₂_right_of_forall₂_const hbase_forall2
            have pmf : Pmf ((G.graphicMatroid ／ S Uacc) ↾ S A') :=
              treesPmf hbase hnonneg' hsumcond
            have hT0mem : (T0, w0) ∈ trees := by
              cases hv : trees with
              | nil => rw [hv] at hhead; simp at hhead
              | cons hd tl =>
                rw [hv] at hhead
                simp only [List.head?_cons, Option.some.injEq] at hhead
                rw [← hhead]
                exact List.mem_cons_self
            have hT0base : ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S T0) := hbase _ hT0mem
            refine ⟨⟨S A', hAE, pmf⟩, congrArg S hAeq, ?_, hAeq ▸ hA1, hAeq ▸ hA2⟩
            have hkey := isBase_restrict_union hAE hI₀ hT0base
            rw [S_append, S_append] at hkey
            rw [← hAeq, ← hI'eq]
            exact hkey

/-- **Soundness of `checkPieces`**: folds `checkPiece_sound` over the whole
raw pieces list, extending a starting `PieceList` (matching the starting
`Uacc`/`I₀acc` invariant) into one covering the final `Uacc'`. Structural
recursion on `raws`, mirroring `checkPieces`'s own recursion exactly. -/
noncomputable def checkPieces_sound {G : Multigraph V E} {toE : Nat → Except String E} :
    ∀ {raws : List RawPiece} {Uacc I₀acc Uacc' : List E} {i : Nat},
      (G.graphicMatroid ↾ (S Uacc)).IsBase (S I₀acc) →
      PieceList G.graphicMatroid (S Uacc) → Uacc.Nodup →
      checkPieces G toE raws Uacc I₀acc i = Except.ok Uacc' →
      PSigma (fun _ : PieceList G.graphicMatroid (S Uacc') => Uacc'.Nodup)
  | [], Uacc, I₀acc, Uacc', i, _, pl, hNodup, hok => by
      unfold checkPieces at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      exact ⟨(congrArg S hok) ▸ pl, hok ▸ hNodup⟩
  | raw :: rest, Uacc, I₀acc, Uacc', i, hI₀, pl, hNodup, hok => by
      unfold checkPieces at hok
      split at hok
      next => exact absurd hok (by simp)
      next hpieceok =>
        rename_i pA pI0
        obtain ⟨p, hpA, hI₀', hpNodup, hpDisj⟩ := checkPiece_sound hI₀ hpieceok
        have hUeq : (S Uacc ∪ p.A : Set E) = S (Uacc ++ pA) := by rw [hpA, S_append]
        have pl' : PieceList G.graphicMatroid (S (Uacc ++ pA)) := hUeq ▸ PieceList.cons pl p
        have hNodup' : (Uacc ++ pA).Nodup :=
          List.nodup_append.mpr ⟨hNodup, hpNodup,
            fun a ha b hb heq => hpDisj b hb (heq ▸ ha)⟩
        exact checkPieces_sound hI₀' pl' hNodup' hok

theorem natToFin_val {bound n : Nat} {f : Fin bound} (h : natToFin bound n = Except.ok f) :
    f.val = n := by
  unfold natToFin at h
  split_ifs at h with hlt
  simp only [Except.ok.injEq] at h
  rw [← h]

/-- **Bridges `buildGraph`'s checked, `Fin`-indexed endpoints back to the
raw JSON `Nat` pairs.** Needed to apply the Kruskal admissibility axiom
(stated over `cg.endpoints`, `Admissibility.lean`) to what `checkCertificate`
actually calls `Kruskal.run` on (`raw.graph.edges.toArray`, plain `Nat`
pairs, unconverted). -/
theorem buildGraph_edges_val {raw : RawGraph} {cg : CheckedGraph}
    (h : buildGraph raw = Except.ok cg) :
    cg.endpoints.toList.map (fun p : Fin cg.n × Fin cg.n => (p.1.val, p.2.val)) = raw.edges := by
  unfold buildGraph at h
  simp only [bind, Except.bind] at h
  split at h
  next => exact absurd h (by simp)
  next hm =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rw [Array.mapM_eq_mapM_toList] at hm
    simp only [Functor.map, Except.map] at hm
    split at hm
    next => exact absurd hm (by simp)
    next hm' =>
      simp only [Except.ok.injEq] at hm
      have hforall2 := mapM_ok_forall₂ _ hm'
      have hlist := hforall2.imp (fun (p : Nat × Nat) (q : Fin raw.num_vertices × Fin raw.num_vertices) hpq => by
        show q.1.val = p.1 ∧ q.2.val = p.2
        split at hpq
        next => exact absurd hpq (by simp)
        next hu =>
          rename_i u'
          split at hpq
          next => exact absurd hpq (by simp)
          next hv =>
            rename_i v'
            have hpq' : (u', v') = q := by simpa [pure, Except.pure] using hpq
            refine ⟨?_, ?_⟩
            · rw [← hpq']; exact natToFin_val hu
            · rw [← hpq']; exact natToFin_val hv)
      dsimp only
      rw [← hm, List.toList_toArray]
      clear hforall2 hm hm'
      generalize hedges : raw.edges = edges at hlist ⊢
      clear hedges
      induction hlist with
      | nil => rfl
      | cons hpq _ ih => simp only [List.map_cons, hpq.1, hpq.2, ih]

/-- **The generic checker-to-proof-term soundness theorem.** If
`checkCertificate` accepts a raw certificate, then (a) a genuine `Pmf` on
the certificate's graph's spanning trees exists, built entirely from the
certificate's own `pieces` data via `checkPieces_sound`/`PieceList.glueAllGraph`
(no hand-transcription, works for *any* accepted certificate, not just
`house`), and (b) the certificate's own computed `rho` really is admissible
-- the Kruskal-admissibility axiom (`Admissibility.lean`), applied for real
this time, not sidestepped by a uniform-density special case the way
`HouseCert.lean`'s `houseCertificateOptimal` was.

**Scope, deliberately**: this does not (yet) prove the two halves are the
*same* certificate's `(rho, mu)` pair in the sense `certificate_optimality`
needs (`rho = mu.marginal / sqNorm mu.marginal`) -- that needs a further
correspondence between `sumTreeContributions`'s `Array.set!`/`getD`-based
computation and `PieceList.marginalSum`'s clean recursive sum, which is
real, separate follow-up work (comparable in size to `checkPiece_sound`
above), not something this theorem silently assumes. Tracked in
`Certification_Plan.md`'s PR5 entry. -/
theorem checkCertificate_sound (raw : RawCertificate) (hok : checkCertificate raw = Except.ok ()) :
    ∃ (n m : Nat) (G : Multigraph (Fin n) (Fin m)) (ρ : CertDensity (Fin m))
      (_μ : Pmf G.graphicMatroid), IsAdmissible G.graphicMatroid ρ := by
  unfold checkCertificate at hok
  split_ifs at hok with hver
  · dsimp only at hok
    cases hcg : buildGraph raw.graph with
    | error e => rw [hcg] at hok; simp [bind, pure, Except.pure, Except.bind] at hok
    | ok cg =>
      rw [hcg] at hok
      simp only [bind, Except.bind] at hok
      cases hUacc : checkPieces cg.toMultigraph (natToFin cg.endpoints.size) raw.pieces [] [] 0 with
      | error e => rw [hUacc] at hok; simp [bind, pure, Except.pure, Except.bind] at hok
      | ok Uacc =>
        rw [hUacc] at hok
        simp only [bind, Except.bind] at hok
        split_ifs at hok with hlen
        split at hok
        next => exact absurd hok (by simp)
        next hEta =>
          split at hok
          next => exact absurd hok (by simp)
          next hDeclEta =>
            split at hok
            next => exact absurd hok (by simp)
            next hEtaCheck =>
              split at hok
              next => exact absurd hok (by simp)
              next hNormSq =>
                split at hok
                next => exact absurd hok (by simp)
                next hDeclRho =>
                  split at hok
                  next => exact absurd hok (by simp)
                  next hRhoCheck =>
                    split at hok
                    next => exact absurd hok (by simp)
                    next hMst =>
                      done
  · simp only [bind, Except.bind] at hok
    exact absurd hok (by simp)
