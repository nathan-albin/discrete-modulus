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
certificate `checkCertificate` accepts, not a hand-picked example:
`checkCertificate_sound` shows accepting implies a real `Pmf
G.graphicMatroid` and admissible `ρ` exist with `certificate_optimality`'s
conclusion, and `checkCertificate_optimal` (the file's capstone) wires that
directly into `certificate_optimality` itself: for any accepted
certificate, its `ρ` and `μ` really are simultaneously optimal.

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
        simp [bind, Except.bind] at h
      | ok b =>
        rw [hfa] at h
        cases htr : t.mapM f with
        | error e =>
          rw [htr] at h
          simp [bind, Except.bind] at h
        | ok bs =>
          rw [htr] at h
          simp only [bind, pure, Except.pure, Except.bind,
            Except.ok.injEq] at h
          subst h
          exact List.Forall₂.cons hfa (mapM_ok_forall₂ f htr)

end MonadHelpers

section ArrayFoldMarginal

/-! ## Bridging `sumTreeContributions`'s imperative `Array.set!`/`getD` fold to a
declarative sum.

`sumTreeContributions` (`CertChecker.lean`) computes a certificate's `η` by
mutating an `Array ℚ` accumulator, one edge at a time, across three nested
folds (pieces, then a piece's own trees, then a tree's own edges). The
`Pmf`/`PieceList` side (`Family.lean`/`Glue.lean`) computes the "same"
quantity as a plain recursive sum (`Pmf.marginal`, `PieceList.marginalSum`).
This section proves the two agree, one generic lemma reused at all three
fold levels: `foldlM_getD_eq_of_forall` says that *if* every individual step
of a monadic `Array ℚ`-accumulating fold adds a known per-element
`contrib`ution at a given index (and preserves the array's size), *then* the
whole fold's final value at that index is the starting value plus the sum of
every element's contribution — regardless of how many elements there are or
what else the step does. Applied at the edge level, `contrib` is an
indicator (`treesPmf_marginal`'s own shape); at the tree and piece levels,
`contrib` is just "the next level's already-established total," so the same
lemma reproduces `Pmf.marginal`'s and `PieceList.marginalSum`'s recursive
sums exactly, without needing separate bespoke inductions at each level. -/

theorem getD_set!_self {α : Type*} (xs : Array α) {i : Nat} (hi : i < xs.size) (x d : α) :
    (xs.set! i x).getD i d = x := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt hi, Option.getD_some]

theorem getD_set!_ne {α : Type*} (xs : Array α) {i j : Nat} (hij : i ≠ j) (x d : α) :
    (xs.set! i x).getD j d = xs.getD j d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne hij, ← Array.getD_eq_getD_getElem?]

/-- **The generic fold-vs-sum bridge.** If every step of a monadic
`Array ℚ`-accumulating fold, *for elements actually in the list being
folded* (`hstep` is only required pointwise on `a ∈ l`, not for every `a` of
the type -- some levels below need a per-element side-fact, e.g. "this
tree's own edge list has no duplicates", that isn't derivable from the step
function alone), preserves the array's size and adds exactly `contrib a i`
at index `i` (for *every* `i`, not just one -- this is what lets the lemma
apply uniformly regardless of whether `a`'s own contribution happens to be
zero at `i`), then folding the whole list adds up every element's
contribution, matching a plain `List.sum`. Proved by structural induction on
the list, mirroring `List.foldlM`'s own recursion exactly (the same style
`mapM_ok_forall₂` above already uses for `List.mapM`). -/
theorem foldlM_getD_eq_of_forall {α : Type*} {bound : Nat}
    (step : Array ℚ → α → Except String (Array ℚ)) (contrib : α → Fin bound → ℚ) :
    ∀ (l : List α), (∀ a ∈ l, ∀ (acc acc' : Array ℚ), acc.size = bound →
        step acc a = Except.ok acc' →
        acc'.size = bound ∧ ∀ i : Fin bound, acc'.getD i.val 0 = acc.getD i.val 0 + contrib a i) →
      ∀ (acc0 acc0' : Array ℚ), acc0.size = bound →
      l.foldlM step acc0 = Except.ok acc0' →
      ∀ i : Fin bound, acc0'.getD i.val 0 = acc0.getD i.val 0 + (l.map (fun a => contrib a i)).sum
  | [], _, acc0, acc0', _, hok, i => by
      rw [List.foldlM_nil] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst hok
      simp
  | a :: as, hstep, acc0, acc0', hsz, hok, i => by
      rw [List.foldlM_cons] at hok
      cases hstepres : step acc0 a with
      | error e => rw [hstepres] at hok; simp [bind, Except.bind] at hok
      | ok acc1 =>
        rw [hstepres] at hok
        simp only [bind, Except.bind] at hok
        obtain ⟨hsz1, hcontrib1⟩ := hstep a List.mem_cons_self acc0 acc1 hsz hstepres
        have hstep' : ∀ a ∈ as, ∀ (acc acc' : Array ℚ), acc.size = bound →
            step acc a = Except.ok acc' →
            acc'.size = bound ∧ ∀ i : Fin bound, acc'.getD i.val 0 = acc.getD i.val 0 + contrib a i :=
          fun a' ha' => hstep a' (List.mem_cons_of_mem a ha')
        rw [foldlM_getD_eq_of_forall step contrib as hstep' acc1 acc0' hsz1 hok i, hcontrib1 i,
          List.map_cons, List.sum_cons]
        ring

/-- **Size-preservation companion to `foldlM_getD_eq_of_forall`**, split out
separately since not every call site needs the value-level conclusion (and
carrying both in one statement would force every caller to thread a size
proof through the `contrib` bookkeeping even when only size is needed). Same
hypotheses shape, same proof strategy. -/
theorem foldlM_size_eq_of_forall {α : Type*} {bound : Nat}
    (step : Array ℚ → α → Except String (Array ℚ)) :
    ∀ (l : List α), (∀ a ∈ l, ∀ (acc acc' : Array ℚ), acc.size = bound →
        step acc a = Except.ok acc' → acc'.size = bound) →
      ∀ (acc0 acc0' : Array ℚ), acc0.size = bound →
      l.foldlM step acc0 = Except.ok acc0' → acc0'.size = bound
  | [], _, acc0, acc0', hsz, hok => by
      rw [List.foldlM_nil] at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      subst hok
      exact hsz
  | a :: as, hstep, acc0, acc0', hsz, hok => by
      rw [List.foldlM_cons] at hok
      cases hstepres : step acc0 a with
      | error e => rw [hstepres] at hok; simp [bind, Except.bind] at hok
      | ok acc1 =>
        rw [hstepres] at hok
        simp only [bind, Except.bind] at hok
        exact foldlM_size_eq_of_forall step as
          (fun a' ha' => hstep a' (List.mem_cons_of_mem a ha'))
          acc1 acc0' (hstep a List.mem_cons_self acc0 acc1 hsz hstepres) hok

/-- A `Nodup` list's indicator sum picks out membership: summing `w` at
every occurrence of `a` in `l` gives `w` if `a ∈ l` and `0` otherwise,
*because* `Nodup` rules out `a` occurring twice (without it, a repeated `a`
would double-count). This is what lets `sumTreeContributions`'s per-edge
array fold -- which really does add `w` once per *list* occurrence -- match
`treesPmf_marginal`'s Set-indicator formula, which is blind to how many
times an edge appears in a tree's own (checked-`Nodup`) edge list. -/
theorem sum_map_ite_eq_of_nodup {α : Type*} [DecidableEq α] (w : ℚ) (a : α) :
    ∀ {l : List α}, l.Nodup →
      (l.map (fun x => if x = a then w else 0)).sum = if a ∈ l then w else 0
  | [], _ => by simp
  | b :: l, hnodup => by
      rw [List.nodup_cons] at hnodup
      obtain ⟨hbl, hl⟩ := hnodup
      rw [List.map_cons, List.sum_cons, sum_map_ite_eq_of_nodup w a hl]
      by_cases hba : b = a
      · subst hba
        simp [hbl]
      · by_cases ha : a ∈ l
        · simp [hba, ha, Ne.symm hba]
        · simp [hba, ha, Ne.symm hba]

/-- If two lists are pointwise related by "applying `f`/`g` respectively
gives the same value", their `f`-mapped and `g`-mapped images (hence sums)
agree -- used to transport a per-element correspondence (`toE eNat = Except.ok e`
implies the raw and converted contributions agree) up to the whole list. -/
theorem forall₂_map_eq {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ (fun a b => f a = g b) l1 l2 →
      l1.map f = l2.map g
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h ht => by
      rw [List.map_cons, List.map_cons, h, forall₂_map_eq ht]

/-- **Level 1: the edge-within-a-tree fold matches `treesPmf_marginal`'s
term.** `sumTreeContributions`'s innermost fold, over one tree's own raw
edge-index list, converting each via `toE` and adding the tree's weight `w`
at that edge -- given the converted list is `Nodup` (`checkTree_nodup`) and
matches `T` (`hconv`, the same conversion `checkPiece`'s own parse already
performs), the fold's net effect at any edge `i` is exactly the indicator
`if i ∈ S T then w else 0`, matching `treesPmf_marginal`'s own per-tree
term. -/
theorem edgeFold_getD_eq {bound : Nat} (toE : Nat → Except String (Fin bound)) (w : ℚ)
    (T_raw : List Nat) (T : List (Fin bound)) (hconv : T_raw.mapM toE = Except.ok T)
    (hNodup : T.Nodup) (acc0 acc1 : Array ℚ) (hsz : acc0.size = bound)
    (hfold : T_raw.foldlM
        (fun acc eNat => do
          let e ← toE eNat
          pure (acc.set! e.val (acc.getD e.val 0 + w)))
        acc0 = Except.ok acc1)
    (i : Fin bound) :
    acc1.size = bound ∧ acc1.getD i.val 0 = acc0.getD i.val 0 + (if i ∈ S T then w else 0) := by
  set edgeContrib : Nat → Fin bound → ℚ :=
    fun eNat j => match toE eNat with | Except.ok e => if e = j then w else 0 | Except.error _ => 0
    with hedgeContrib
  have hstep : ∀ eNat ∈ T_raw, ∀ (acc acc' : Array ℚ), acc.size = bound →
      (do let e ← toE eNat; pure (acc.set! e.val (acc.getD e.val 0 + w)) : Except String (Array ℚ))
        = Except.ok acc' →
      acc'.size = bound ∧ ∀ j : Fin bound, acc'.getD j.val 0 = acc.getD j.val 0 + edgeContrib eNat j := by
    intro eNat _ acc acc' hsz' hstepok
    cases hte : toE eNat with
    | error e => rw [hte] at hstepok; simp [bind, Except.bind] at hstepok
    | ok e =>
      rw [hte] at hstepok
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hstepok
      subst hstepok
      refine ⟨by rw [Array.size_set!]; exact hsz', fun j => ?_⟩
      simp only [hedgeContrib, hte]
      by_cases hej : e = j
      · subst hej
        rw [getD_set!_self acc (by rw [hsz']; exact e.isLt) _ 0, if_pos rfl]
      · rw [getD_set!_ne acc (fun h => hej (Fin.ext h)) _ 0, if_neg hej, add_zero]
  refine ⟨foldlM_size_eq_of_forall
    (fun acc eNat => (do let e ← toE eNat; pure (acc.set! e.val (acc.getD e.val 0 + w)) :
      Except String (Array ℚ)))
    T_raw (fun eNat hm acc acc' hsz' h => (hstep eNat hm acc acc' hsz' h).1) acc0 acc1 hsz hfold, ?_⟩
  have hres := foldlM_getD_eq_of_forall
    (fun acc eNat => (do let e ← toE eNat; pure (acc.set! e.val (acc.getD e.val 0 + w)) :
      Except String (Array ℚ)))
    edgeContrib T_raw hstep acc0 acc1 hsz hfold i
  rw [hres]
  congr 1
  have hforall2 := mapM_ok_forall₂ toE hconv
  have hmapeq : T_raw.map (fun eNat => edgeContrib eNat i) = T.map (fun e => if e = i then w else 0) :=
    forall₂_map_eq (hforall2.imp (fun eNat e he => by rw [hedgeContrib]; simp [he]))
  rw [hmapeq, sum_map_ite_eq_of_nodup w i hNodup]
  rfl

end ArrayFoldMarginal

section NormSqBridge

/-! ## Bridging `checkCertificate`'s array-level `normSq` fold to `sqNorm`.

`checkCertificate` (`CertChecker.lean`) computes the sum of squared etas as a
plain `List.foldl` over `List.range m`, since that's the natural thing to
write against an `Array ℚ` accumulator at runtime. `certificate_optimality`
(`Optimality.lean`) is stated in terms of `sqNorm`, a `Finset.sum` over
`Fin m`. This section shows the two agree, so a certificate's declared `rho`
can be shown to literally equal `eta / sqNorm eta` in the vocabulary the
optimality lemma needs, not just the array-level vocabulary the runtime
checker happens to use. -/

theorem list_range_foldl_add_eq_sum_range (m : Nat) (f : Nat → ℚ) :
    (List.range m).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; simp

/-- The array-level `normSq` fold `checkCertificate` computes agrees with
`sqNorm` applied to the array read off as a `Fin m → ℚ` function --
unconditionally, regardless of the array's actual size (out-of-range reads
on either side are `0`, contributing nothing to either sum). -/
theorem normSq_eq_sqNorm (m : Nat) (computedEta : Array ℚ) :
    (List.range m).foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
      = sqNorm (fun e : Fin m => computedEta.getD e.val 0) := by
  rw [list_range_foldl_add_eq_sum_range,
    ← Fin.sum_univ_eq_sum_range (fun i => computedEta.getD i 0 * computedEta.getD i 0) m]
  unfold sqNorm
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- `Array.map`'s effect on `getD`, specialized to division: division's
default-preserving property (`0 / c = 0`) means the two sides agree
regardless of whether the index is in bounds. -/
theorem array_getD_map_div (arr : Array ℚ) (i : Nat) (c : ℚ) :
    (arr.map (· / c)).getD i 0 = arr.getD i 0 / c := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases h : arr[i]? with _ | x <;> simp

end NormSqBridge

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

/-! ## Generic `S`-manipulation lemmas

Small facts about `CertChecker.S` (the edge-set-of-a-list abbreviation),
stated over an arbitrary `V`/`E`/`G` -- none of these actually depend on
`G` except `forall_diff_not_isForest_of_list_all`. -/

omit [DecidableEq E] [Fintype E] in
theorem S_ne_of_mem_not_mem {l₁ l₂ : List E} {x : E} (hx1 : x ∈ l₁) (hx2 : x ∉ l₂) :
    (S l₁ : Set E) ≠ S l₂ := by
  intro h; apply hx2; have hx1' : x ∈ S l₁ := hx1; rw [h] at hx1'; exact hx1'

omit [DecidableEq E] [Fintype E] in
theorem S_subset_of_forall_mem {l₁ l₂ : List E} (h : ∀ x ∈ l₁, x ∈ l₂) : S l₁ ⊆ S l₂ := h

omit [DecidableEq E] [Fintype E] in
theorem S_append (l₁ l₂ : List E) : (S l₁ : Set E) ∪ S l₂ = S (l₁ ++ l₂) := by
  ext x; simp [S, List.mem_append]

omit [DecidableEq E] [Fintype E] in
theorem S_nil : (S ([] : List E) : Set E) = ∅ := by ext x; simp [S]

/-- A `Nodup` list whose length matches `Fintype.card E` must enumerate
every element of `E` -- used to turn `checkCertificate`'s partition-
completeness check (`Uacc.length = m`, together with `checkPieces`'s own
disjointness invariant giving `Uacc.Nodup`) into the `S Uacc = Set.univ`
fact `PieceList.glueAllGraph` needs to fold a certificate's pieces into a
genuine top-level `Pmf`. -/
theorem S_eq_univ_of_nodup_length {l : List E} (hnodup : l.Nodup)
    (hlen : l.length = Fintype.card E) : (S l : Set E) = Set.univ := by
  have hcard : l.toFinset.card = Fintype.card E := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have huniv : l.toFinset = (Finset.univ : Finset E) := Finset.eq_univ_of_card _ hcard
  have hSeq : (S l : Set E) = (l.toFinset : Set E) := by
    ext x; simp [S]
  rw [hSeq, huniv, Finset.coe_univ]

omit [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] in
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
omit [Fintype E] in
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

omit [Fintype V] [Fintype E] in
/-- **`checkTree`'s first check, isolated.** A declared tree's own edge list
has no duplicate edge index -- needed (alongside `checkTree_sound`'s `IsBase`
conclusion) to know that `sumTreeContributions`'s per-edge array fold over
this same list touches each of the tree's edges exactly once, matching
`treesPmf_marginal`'s Set-indicator formula (which is blind to list
duplicates) term for term. -/
theorem checkTree_nodup {G : Multigraph V E} {I₀acc A T : List E}
    (hok : checkTree G I₀acc A T = Except.ok PUnit.unit) : T.Nodup := by
  unfold checkTree at hok
  simp only [check] at hok
  split_ifs at hok with h1 h2
  · exact of_decide_eq_true h1
  all_goals simp [bind, Except.bind] at hok

omit [Fintype V] in
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

omit [DecidableEq V] [Fintype V] [DecidableEq E] in
theorem subset_contract_E_of_disjoint {G : Multigraph V E} {prev A : List E}
    (hdisj : ∀ e ∈ A, e ∉ prev) :
    S A ⊆ (G.graphicMatroid ／ (S prev)).E := by
  rw [Matroid.contract_ground, graphicMatroid_E]
  refine Set.subset_sdiff.mpr ⟨Set.subset_univ _, ?_⟩
  rw [Set.disjoint_left]
  intro e he hep
  exact hdisj e he hep

omit [DecidableEq E] [Fintype E] in
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
    exact (Set.subset_sdiff.mp h).2
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

/-- The companion fact to `forall₂_right_of_forall₂_const`, for a relation
that isn't const in its left argument: given `a` on the left, there's a
*specific* related `b` on the right satisfying the full relation `R a b` --
used to recover, for one specific declared tree `t`, the exact converted
`(edges, weight)` pair and per-tree facts (`IsBase`, `Nodup`, the raw
conversion) that `checkPiece`'s own parse already established for it. -/
theorem forall₂_exists_of_mem_left {α β : Type*} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, List.Forall₂.nil, a, ha => absurd ha List.not_mem_nil
  | _, _, List.Forall₂.cons h ht, a, ha => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨b, hb, hrb⟩ := forall₂_exists_of_mem_left ht a ha'
        exact ⟨b, List.mem_cons_of_mem _ hb, hrb⟩

open Classical in
/-- **Specialized to `E := Fin m`** (rather than the file's usual abstract
`E`), and extended with one more conjunct beyond the matroid/base facts: a
correspondence between `sumTreeContributions`'s per-piece imperative fold
(`CertChecker.lean`) and `p.pmf.marginal` (`treesPmf_marginal`/`Family.lean`).
The specialization is forced by `sumTreeContributions` itself, which is
`Fin m`-indexed for the same reason its own docstring gives: no computable
`E → Fin m` projection exists generically. The only actual caller
(`checkPieces_sound` below) is being extended the same way, so nothing else
depends on this having stayed abstract. -/
noncomputable def checkPiece_sound {m : Nat} {G : Multigraph V (Fin m)} {Uacc I₀acc : List (Fin m)}
    {raw : RawPiece} {toE : Nat → Except String (Fin m)} {A I₀acc' : List (Fin m)}
    (hI₀ : (G.graphicMatroid ↾ (S Uacc)).IsBase (S I₀acc))
    (hok : checkPiece G Uacc I₀acc raw toE = Except.ok (A, I₀acc')) :
    Σ' (p : Piece G.graphicMatroid (S Uacc)),
      p.A = S A ∧ (G.graphicMatroid ↾ (S (Uacc ++ A))).IsBase (S I₀acc') ∧
      A.Nodup ∧ (∀ e ∈ A, e ∉ Uacc) ∧
      (∀ (acc0 acc1 : Array ℚ), acc0.size = m →
        raw.local_pmf.trees.foldlM
          (fun acc t => do
            let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
            let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
            t.edges.foldlM
              (fun acc eNat => do
                let e ← toE eNat
                pure (acc.set! e.val (acc.getD e.val 0 + w)))
              acc)
          acc0 = Except.ok acc1 →
        acc1.size = m ∧ ∀ i : Fin m, acc1.getD i.val 0 = acc0.getD i.val 0 + p.pmf.marginal i) := by
  unfold checkPiece at hok
  simp only [check] at hok
  cases hA' : raw.edges.mapM toE with
  | error e =>
    rw [hA'] at hok
    simp [bind, Except.bind] at hok
  | ok A' =>
    rw [hA'] at hok
    simp only [bind, Except.bind] at hok
    (split_ifs at hok with h1 h2; simp only [pure, Except.pure] at hok)
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
            have hpiece_forall2 : List.Forall₂ (fun (rawT : RawTree) (pair : List (Fin m) × ℚ) =>
                ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S pair.1) ∧ pair.1.Nodup ∧
                rawT.edges.mapM toE = Except.ok pair.1) raw.local_pmf.trees trees := by
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
                    exact ⟨checkTree_sound hI₀ hAE hct, checkTree_nodup hct, hmapedges⟩
            have hbase : ∀ t ∈ trees, ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S t.1) :=
              forall₂_right_of_forall₂_const (hpiece_forall2.imp (fun _ _ h => h.1))
            set pmf : Pmf ((G.graphicMatroid ／ S Uacc) ↾ S A') :=
              treesPmf hbase hnonneg' hsumcond with hpmf
            have hT0mem : (T0, w0) ∈ trees := by
              cases hv : trees with
              | nil => rw [hv] at hhead; simp at hhead
              | cons hd tl =>
                rw [hv] at hhead
                simp only [List.head?_cons, Option.some.injEq] at hhead
                rw [← hhead]
                exact List.mem_cons_self
            have hT0base : ((G.graphicMatroid ／ S Uacc) ↾ S A').IsBase (S T0) := hbase _ hT0mem
            have hmarginal : ∀ (acc0 acc1 : Array ℚ), acc0.size = m →
                raw.local_pmf.trees.foldlM
                  (fun acc t => do
                    let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
                    let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
                    t.edges.foldlM
                      (fun acc eNat => do
                        let e ← toE eNat
                        pure (acc.set! e.val (acc.getD e.val 0 + w)))
                      acc)
                  acc0 = Except.ok acc1 →
                acc1.size = m ∧ ∀ i : Fin m, acc1.getD i.val 0 = acc0.getD i.val 0 + pmf.marginal i := by
              set treeContrib : RawTree → Fin m → ℚ := fun t j =>
                if t.weight.2 = 0 then 0 else
                match t.edges.mapM toE with
                | Except.ok T => if j ∈ S T then (t.weight.1 : ℚ) / (t.weight.2 : ℚ) else 0
                | Except.error _ => 0
                with htreeContrib
              have hstep2 : ∀ t ∈ raw.local_pmf.trees, ∀ (acc acc' : Array ℚ), acc.size = m →
                  (do
                    let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
                    let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
                    t.edges.foldlM
                      (fun acc eNat => do
                        let e ← toE eNat
                        pure (acc.set! e.val (acc.getD e.val 0 + w)))
                      acc : Except String (Array ℚ)) = Except.ok acc' →
                  acc'.size = m ∧ ∀ j : Fin m, acc'.getD j.val 0 = acc.getD j.val 0 + treeContrib t j := by
                intro t ht acc acc' hsz' hstepok
                obtain ⟨pair, -, -, hnodupP, hmapP⟩ :=
                  forall₂_exists_of_mem_left hpiece_forall2 t ht
                simp only [check] at hstepok
                by_cases hw0 : t.weight.2 = 0
                · exfalso
                  rw [if_neg (by simp [hw0])] at hstepok
                  simp [bind, Except.bind] at hstepok
                · have hstepok' : t.edges.foldlM
                      (fun acc eNat => do
                        let e ← toE eNat
                        pure (acc.set! e.val (acc.getD e.val 0 + (t.weight.1 : ℚ) / (t.weight.2 : ℚ))))
                      acc = Except.ok acc' := by
                    rw [if_pos (by simp [hw0])] at hstepok
                    simp only [bind, Except.bind, pure, Except.pure] at hstepok
                    exact hstepok
                  have hcontrib_eq : treeContrib t = fun j => if j ∈ S pair.1 then (t.weight.1 : ℚ) / (t.weight.2 : ℚ) else 0 := by
                    funext j
                    simp only [htreeContrib, hw0, hmapP, if_false]
                  refine ⟨foldlM_size_eq_of_forall
                    (fun acc eNat => (do
                      let e ← toE eNat
                      pure (acc.set! e.val (acc.getD e.val 0 + (t.weight.1 : ℚ) / (t.weight.2 : ℚ))) :
                      Except String (Array ℚ)))
                    t.edges
                    (fun eNat _ acc₁ acc₁' hsz₁ hs => by
                      cases hte : toE eNat with
                      | error e => rw [hte] at hs; simp [bind, Except.bind] at hs
                      | ok e =>
                        rw [hte] at hs
                        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
                        subst hs
                        rw [Array.size_set!]
                        exact hsz₁)
                    acc acc' hsz' hstepok', fun j => ?_⟩
                  rw [hcontrib_eq]
                  exact (edgeFold_getD_eq toE ((t.weight.1 : ℚ) / (t.weight.2 : ℚ)) t.edges pair.1
                    hmapP hnodupP acc acc' hsz' hstepok' j).2
              intro acc0 acc1 hsz hfold
              refine ⟨foldlM_size_eq_of_forall
                (fun acc t => (do
                  let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
                  let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
                  t.edges.foldlM
                    (fun acc eNat => do
                      let e ← toE eNat
                      pure (acc.set! e.val (acc.getD e.val 0 + w)))
                    acc : Except String (Array ℚ)))
                raw.local_pmf.trees (fun t ht acc acc' hsz' hs => (hstep2 t ht acc acc' hsz' hs).1)
                acc0 acc1 hsz hfold, fun i => ?_⟩
              have hres := foldlM_getD_eq_of_forall
                (fun acc t => (do
                  let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
                  let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
                  t.edges.foldlM
                    (fun acc eNat => do
                      let e ← toE eNat
                      pure (acc.set! e.val (acc.getD e.val 0 + w)))
                    acc : Except String (Array ℚ)))
                treeContrib raw.local_pmf.trees hstep2 acc0 acc1 hsz hfold i
              rw [hres]
              congr 1
              have hforall2 := mapM_ok_forall₂ _ htrees
              have hmapeq : raw.local_pmf.trees.map (fun t => treeContrib t i)
                  = trees.map (fun t => if i ∈ S t.1 then t.2 else 0) := by
                refine forall₂_map_eq (hforall2.imp (fun rawT pair hpair => ?_))
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
                      have hwne : rawT.weight.2 ≠ 0 := by
                        by_contra hc
                        simp [hc] at hwcheck
                      simp only [htreeContrib, hwne, hmapedges, if_false]
              rw [hmapeq, ← treesPmf_marginal hbase hnonneg' hsumcond i, hpmf]
            refine ⟨⟨S A', hAE, pmf⟩, congrArg S hAeq, ?_, hAeq ▸ hA1, hAeq ▸ hA2, hmarginal⟩
            have hkey := isBase_restrict_union hAE hI₀ hT0base
            rw [S_append, S_append] at hkey
            rw [← hAeq, ← hI'eq]
            exact hkey

/-- **Soundness of `checkPieces`**: folds `checkPiece_sound` over the whole
raw pieces list, extending a starting `PieceList` (matching the starting
`Uacc`/`I₀acc` invariant) into one covering the final `Uacc'`. Structural
recursion on `raws`, mirroring `checkPieces`'s own recursion exactly.
**Specialized to `E := Fin m`, and extended** with the same kind of
marginal-fold conjunct `checkPiece_sound` gained: given the accumulator
already matches the *starting* `PieceList`'s `marginalSum` and
`sumTreeContributions`'s outer per-piece fold over the same `raws` succeeds,
the result matches the *extended* `PieceList`'s `marginalSum`. No
cross-piece disjointness bookkeeping is needed here beyond what
`checkPiece_sound` already supplies -- each piece's own contribution is
just added on both sides (`PieceList.marginalSum`'s own `cons` case,
matching one step of `sumTreeContributions`'s outer fold exactly). -/
noncomputable def checkPieces_sound {m : Nat} {G : Multigraph V (Fin m)}
    {toE : Nat → Except String (Fin m)} :
    ∀ {raws : List RawPiece} {Uacc I₀acc Uacc' : List (Fin m)} {i : Nat},
      (G.graphicMatroid ↾ (S Uacc)).IsBase (S I₀acc) →
      (pl : PieceList G.graphicMatroid (S Uacc)) → Uacc.Nodup →
      checkPieces G toE raws Uacc I₀acc i = Except.ok Uacc' →
      Σ' (pl' : PieceList G.graphicMatroid (S Uacc')), Uacc'.Nodup ∧
        (∀ (acc0 accf : Array ℚ), acc0.size = m →
          (∀ e : Fin m, acc0.getD e.val 0 = pl.marginalSum e) →
          raws.foldlM
            (fun acc piece =>
              piece.local_pmf.trees.foldlM
                (fun acc t => do
                  let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
                  let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
                  t.edges.foldlM
                    (fun acc eNat => do
                      let e ← toE eNat
                      pure (acc.set! e.val (acc.getD e.val 0 + w)))
                    acc)
                acc)
            acc0 = Except.ok accf →
          ∀ e : Fin m, accf.getD e.val 0 = pl'.marginalSum e)
  | [], Uacc, I₀acc, Uacc', i, _, pl, hNodup, hok => by
      unfold checkPieces at hok
      simp only [pure, Except.pure, Except.ok.injEq] at hok
      refine ⟨(congrArg S hok) ▸ pl, hok ▸ hNodup, ?_⟩
      intro acc0 accf hsz hmarg0 hfold e
      rw [List.foldlM_nil] at hfold
      simp only [pure, Except.pure, Except.ok.injEq] at hfold
      rw [← hfold, hmarg0 e, PieceList.marginalSum_cast]
  | raw :: rest, Uacc, I₀acc, Uacc', i, hI₀, pl, hNodup, hok => by
      unfold checkPieces at hok
      split at hok
      next => exact absurd hok (by simp)
      next hpieceok =>
        rename_i pA pI0
        obtain ⟨p, hpA, hI₀', hpNodup, hpDisj, hpMarg⟩ := checkPiece_sound hI₀ hpieceok
        have hUeq : (S Uacc ∪ p.A : Set (Fin m)) = S (Uacc ++ pA) := by rw [hpA, S_append]
        set pl' : PieceList G.graphicMatroid (S (Uacc ++ pA)) := hUeq ▸ PieceList.cons pl p with hpl'
        have hNodup' : (Uacc ++ pA).Nodup :=
          List.nodup_append.mpr ⟨hNodup, hpNodup,
            fun a ha b hb heq => hpDisj b hb (heq ▸ ha)⟩
        obtain ⟨pl'', hNodup'', hMarg''⟩ := checkPieces_sound hI₀' pl' hNodup' hok
        refine ⟨pl'', hNodup'', ?_⟩
        intro acc0 accf hsz hmarg0 hfold
        rw [List.foldlM_cons] at hfold
        cases hstepres : (raw.local_pmf.trees.foldlM
            (fun acc t => do
              let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
              let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
              t.edges.foldlM
                (fun acc eNat => do
                  let e ← toE eNat
                  pure (acc.set! e.val (acc.getD e.val 0 + w)))
                acc)
            acc0 : Except String (Array ℚ)) with
        | error err => rw [hstepres] at hfold; simp [bind, Except.bind] at hfold
        | ok acc1 =>
          rw [hstepres] at hfold
          simp only [bind, Except.bind] at hfold
          have hp1 := hpMarg acc0 acc1 hsz hstepres
          have hacc1marg : ∀ e' : Fin m, acc1.getD e'.val 0 = pl'.marginalSum e' := by
            intro e'
            rw [hp1.2 e', hmarg0 e', hpl', PieceList.marginalSum_cast hUeq (PieceList.cons pl p) e']
            rfl
          exact hMarg'' acc1 accf hp1.1 hacc1marg hfold

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
(no hand-transcription, works for *any* accepted certificate), (b) the
certificate's own computed `rho` really is admissible -- always via the
Kruskal-admissibility axiom (`Admissibility.lean`), unconditionally, even
for a certificate whose `rho` happens to be uniform (where
`Admissibility.lean`'s axiom-free `isAdmissible_const_div_ncard_of_isBase`
would also apply, but this generic theorem doesn't special-case that) --
and (c) **the gap this
file's module docstring flagged is now closed**: the certificate's own
`computedEta` (`sumTreeContributions`'s output, the same one `eta`/`rho`'s
runtime check in `checkCertificate` is built from) is, as a function,
*exactly* this same `μ`'s marginal -- not just "some pmf exists" and
"some computed eta exists" separately. This is what
`checkPiece_sound`/`checkPieces_sound`'s new marginal-fold conjuncts (above)
were built for: `hMargFinal`, applied to `sumTreeContributions`'s own
starting accumulator (`Array.replicate m 0`, matching `pl0 = PieceList.nil`'s
`marginalSum = 0`), gives this directly.

**Closed**: `ρ` (the certificate's declared, *normalized* density) is shown
to equal `η / sqNorm η` in the `CertDensity`/`sqNorm` vocabulary
`certificate_optimality` needs, via `normSq_eq_sqNorm`/`array_getD_map_div`
(above) bridging the array-level `normSq` fold `checkCertificate` computes
to the `Finset.sum`-based `sqNorm` (`Family.lean`). See
`checkCertificate_optimal` below, which wires this all the way into
`certificate_optimality` itself. -/
theorem checkCertificate_sound (raw : RawCertificate) (hok : checkCertificate raw = Except.ok ()) :
    ∃ (n m : Nat) (G : Multigraph (Fin n) (Fin m)) (toE : Nat → Except String (Fin m))
      (computedEta : Array ℚ) (ρ : CertDensity (Fin m)) (μ : Pmf G.graphicMatroid),
      sumTreeContributions m toE raw.pieces = Except.ok computedEta ∧
      (fun e : Fin m => computedEta.getD e.val 0) = μ.marginal ∧
      sqNorm (fun e : Fin m => computedEta.getD e.val 0) ≠ 0 ∧
      ρ = (fun e : Fin m => computedEta.getD e.val 0 /
        sqNorm (fun e' : Fin m => computedEta.getD e'.val 0)) ∧
      IsAdmissible G.graphicMatroid ρ := by
  unfold checkCertificate at hok
  split_ifs at hok with hver
  · dsimp only at hok
    cases hcg : buildGraph raw.graph with
    | error e => rw [hcg] at hok; simp [bind, Except.bind] at hok
    | ok cg =>
      rw [hcg] at hok
      simp only [bind, Except.bind] at hok
      cases hUacc : checkPieces cg.toMultigraph (natToFin cg.endpoints.size) raw.pieces [] [] 0 with
      | error e => rw [hUacc] at hok; simp at hok
      | ok Uacc =>
        rw [hUacc] at hok
        simp only [] at hok
        split_ifs at hok with hlen
        split at hok
        next => exact absurd hok (by simp)
        next hEta =>
          rename_i computedEta
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
                      -- Build the genuine `Pmf` from `checkPieces`' own soundness proof.
                      have hSnil : (S ([] : List (Fin cg.endpoints.size)) : Set (Fin cg.endpoints.size)) = ∅ :=
                        S_nil
                      have hI₀empty : (cg.toMultigraph.graphicMatroid ↾ (∅ : Set (Fin cg.endpoints.size))).IsBase
                          (∅ : Set (Fin cg.endpoints.size)) := by
                        rw [Matroid.isBase_restrict_iff (by simp)]
                        exact cg.toMultigraph.graphicMatroid.empty_indep.isBasis_self
                      have hI₀ : (cg.toMultigraph.graphicMatroid ↾
                          S ([] : List (Fin cg.endpoints.size))).IsBase (S ([] : List (Fin cg.endpoints.size))) :=
                        hSnil.symm ▸ hI₀empty
                      set pl0 : PieceList cg.toMultigraph.graphicMatroid
                          (S ([] : List (Fin cg.endpoints.size))) :=
                        hSnil.symm ▸ PieceList.nil with hpl0
                      obtain ⟨pl, hNodupFinal, hMargFinal⟩ := checkPieces_sound hI₀ pl0 List.nodup_nil hUacc
                      have hSuniv : (S Uacc : Set (Fin cg.endpoints.size)) = Set.univ :=
                        S_eq_univ_of_nodup_length hNodupFinal (by rw [Fintype.card_fin]; exact hlen)
                      set plUniv : PieceList cg.toMultigraph.graphicMatroid Set.univ :=
                        hSuniv ▸ pl with hplUniv
                      set μ := PieceList.glueAllGraph (N := cg.toMultigraph.graphicMatroid)
                        (graphicMatroid_E cg.toMultigraph) plUniv with hμ
                      have hacc0marg : ∀ e' : Fin cg.endpoints.size,
                          (Array.replicate cg.endpoints.size (0 : ℚ)).getD e'.val 0 = pl0.marginalSum e' := by
                        intro e'
                        have h0 : (Array.replicate cg.endpoints.size (0 : ℚ)).getD e'.val 0 = 0 := by simp
                        rw [h0, hpl0, PieceList.marginalSum_cast hSnil.symm PieceList.nil e']
                        rfl
                      have hEtaMarginal : (fun e : Fin cg.endpoints.size => computedEta.getD e.val 0)
                          = μ.marginal := by
                        funext e
                        rw [hMargFinal (Array.replicate cg.endpoints.size 0) computedEta
                          Array.size_replicate hacc0marg hEta e,
                          ← PieceList.marginalSum_cast hSuniv pl e, ← hplUniv, hμ]
                        unfold PieceList.glueAllGraph
                        rw [Pmf.cast_marginal, PieceList.glueAll_marginal]
                      -- Bridge `checkCertificate`'s `Kruskal.run` call (over the raw JSON edge
                      -- list) to `Admissibility`'s axiom (stated over `cg.endpoints`).
                      have hEdgesEq : cg.endpoints.map (fun p : Fin cg.n × Fin cg.n => (p.1.val, p.2.val))
                          = raw.graph.edges.toArray := by
                        apply Array.toList_inj.mp
                        rw [Array.toList_map, buildGraph_edges_val hcg, List.toList_toArray]
                      have hMstle : 1 ≤ (Kruskal.run cg.n raw.graph.edges.toArray
                          (computedEta.map (fun x => x /
                            List.foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                              (List.range cg.endpoints.size)))).foldl
                          (fun acc i => acc + (computedEta.map (fun x => x /
                            List.foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                              (List.range cg.endpoints.size))).getD i 0) 0 := by
                        have h := check_eq_ok_iff.mp hMst
                        simpa [not_lt] using h
                      rw [← hEdgesEq] at hMstle
                      have hAdm := Kruskal.run_isAdmissible_of_weight_ge_one
                        cg.endpoints (computedEta.map (fun x => x /
                          List.foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                            (List.range cg.endpoints.size))) hMstle
                      -- Bridge the array-level `normSq` fold to `sqNorm`, and its
                      -- nonvanishing check, to the `certificate_optimality` vocabulary.
                      have hNormSqNe : (List.foldl
                          (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                          (List.range cg.endpoints.size)) ≠ 0 := by
                        have h := check_eq_ok_iff.mp hNormSq
                        simpa using h
                      have hηpos : sqNorm (fun e : Fin cg.endpoints.size => computedEta.getD e.val 0) ≠ 0 := by
                        rw [← normSq_eq_sqNorm]; exact hNormSqNe
                      have hρeq : (fun e : Fin cg.endpoints.size => (computedEta.map (fun x => x /
                            List.foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                              (List.range cg.endpoints.size))).getD e.val 0)
                          = (fun e : Fin cg.endpoints.size => computedEta.getD e.val 0 /
                            sqNorm (fun e' : Fin cg.endpoints.size => computedEta.getD e'.val 0)) := by
                        funext e
                        rw [array_getD_map_div, normSq_eq_sqNorm]
                      refine ⟨cg.n, cg.endpoints.size, cg.toMultigraph, natToFin cg.endpoints.size,
                        computedEta, fun e => (computedEta.map (fun x => x /
                          List.foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
                            (List.range cg.endpoints.size))).getD e.val 0, μ, hEta, hEtaMarginal, hηpos,
                        hρeq, hAdm⟩
  · simp only [bind, Except.bind] at hok
    exact absurd hok (by simp)

/-- **Capstone: an accepted certificate is genuinely optimal.** Wires
`checkCertificate_sound`'s existence facts directly into
`certificate_optimality` (`Optimality.lean`) -- the theorem "the verifier
accepts implies the certificate is optimal" ultimately reduces to, for
*any* accepted certificate. If `checkCertificate` accepts a raw
certificate, its (reconstructed) `ρ` minimizes `sqNorm` over every
admissible density on the
certificate's graphic matroid (`ρ` solves the modulus problem), and the
reconstructed `μ`'s marginal minimizes `sqNorm` over the marginals of every
pmf on that matroid's bases (`μ` solves the dual min-norm-point problem) --
both halves of "simultaneously optimal" from the Cauchy-Schwarz duality
argument (`Optimality.lean`'s module docstring). This closes the gap this
file's own module docstring flags -- turning "checker accepts" into a
genuine kernel-checked optimality proof, not just an existence fact. -/
theorem checkCertificate_optimal (raw : RawCertificate) (hok : checkCertificate raw = Except.ok ()) :
    ∃ (n m : Nat) (G : Multigraph (Fin n) (Fin m)) (ρ : CertDensity (Fin m)) (μ : Pmf G.graphicMatroid),
      (∀ ρ' : CertDensity (Fin m), IsAdmissible G.graphicMatroid ρ' → sqNorm ρ ≤ sqNorm ρ') ∧
      (∀ μ' : Pmf G.graphicMatroid, sqNorm μ.marginal ≤ sqNorm μ'.marginal) := by
  obtain ⟨n, m, G, toE, computedEta, ρ, μ, -, hη, hηpos, hρeq, hAdm⟩ := checkCertificate_sound raw hok
  refine ⟨n, m, G, ρ, μ, ?_⟩
  have hopt := certificate_optimality hAdm hη hηpos hρeq
  rwa [hη] at hopt
