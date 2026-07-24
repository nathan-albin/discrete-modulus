import DiscreteModulusCert.IsBaseCheck
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Making `Multigraph.IsForest` decidable on a concrete graph

`IsBaseCheck.lean` reduces a certificate's per-piece `IsBase` check to a pure
graph-combinatorics question — is a candidate edge set `G.IsForest (I₀ ∪ T)`
for the *original* graph `G` — but flagged that `Multigraph.IsForest` itself
wasn't yet known to be `Decidable`/computably checkable. The obstruction: the
natural route through Mathlib, `isAcyclic_iff_forall_isBridge` +
`Reachable`'s `Fintype`-vertex decidability, doesn't synthesize, because
`IsBridge`'s own decidability and a `Fintype`/`Finset` handle on `edgeSet`
aren't wired up.

This file sidesteps `IsBridge` entirely and builds the decision procedure
directly: a verified union-find-style algorithm, phrased as structural
recursion on a `List E` of candidate edges (a certificate's tree is exactly
such a list — an edge-index list), inserting
one edge at a time and using Mathlib's `isAcyclic_sup_fromEdgeSet_iff` (an
honest iff, both directions, transported into `isForest_insert_iff` below) to
decide at each step whether the new edge closes a cycle.

**A subtlety that shaped the design.** The natural first attempt — strong
induction on a `Finset E`, naming a new edge's two endpoints `u v : V` via
`Sym2.exists` before deciding anything — type-checks and proves the right
theorem, but its `Decidable` value gets *stuck* under the kernel's `decide`
reduction: `Sym2.exists` is `Exists`-valued, and extracting `u, v` from it via
`Classical.choice` to pick which `Decidable` branch (`isTrue`/`isFalse`) to
build is exactly the kind of "large elimination" a classical witness can't
support computationally, even though it's perfectly fine *inside* a proof.
Structural recursion on `List E` (rather than well-founded recursion on
`Finset.card`) fixes the *other* half of this: `Finset.strongInductionOn`
compiles to `WellFounded.fix`/`Acc.rec`, which also doesn't reduce well under
`decide`. The fix for both, combined:
- Recurse on `List E` via ordinary structural pattern matching (`[]` /
  `a :: rest`) — always reduces under `decide`, no well-founded recursion.
- Never *name* an edge's endpoints to decide which branch to take. Instead,
  `decidableIsForestInsertOfComponents`/`decidableIsForestInsertOfList`
  decide "is this edge already addable without closing a cycle" as a
  `Finset`-level membership check (`∃ c ∈ comps, edgeVerts (G.endpoints a) ⊆
  c`) directly on the `Sym2 V` edge value, via `edgeVerts` (itself built
  from `Sym2.lift`, so already branch-free at the value level). Naming the
  endpoints (`induction huv : G.endpoints a with | _ u v => ...`, i.e.
  `Sym2.ind`) is then only ever needed *inside* the resulting proof
  obligations (`Prop`-to-`Prop` elimination, always fine), never to pick
  the `Decidable` branch.

Both fixes were confirmed necessary and sufficient by direct experiment
(`#eval`/`decide` on a 3-cycle test graph) before settling on this design.

**Performance history (two fixes, not one).** The design above type-checks
and is correct at any size, but went through two rounds of genuine
algorithmic traps, not just kernel-reduction inconveniences:
1. Originally wired to Mathlib's own `DecidableRel Reachable` instance for
   "are these endpoints already connected" — built by transporting
   decidability across `reachable_iff_exists_finsetWalkLength_nonempty`,
   whose witness search (`finsetWalkLength`) enumerates *every walk* of
   each candidate length by branching over every neighbor at every step,
   no visited-set pruning at all — exponential in `Fintype.card V`,
   confirmed directly to hang for minutes on a 190-edge/20-vertex
   nearly-complete piece even under `native_decide` (compiled code, so a
   genuinely exponential computation, not a `decide`-vs-`native_decide`
   reduction-strategy artifact).
2. Replaced with a textbook bounded BFS closure over plain `Finset`
   operations (polynomial, not exponential) — a real fix, but one that
   still scanned `Finset.univ` (the *whole* graph's vertex `Fintype`) on
   every round, regardless of how few vertices a given piece actually
   touches. Confirmed via `perf` to still dominate real `verify_cert`
   runtime on `nested.certificate.json` (60 vertices total across all
   pieces, but any one piece touches only ~20 of them): ~25s of a ~26s
   total run, almost entirely in the per-round adjacency scan.

Both are now replaced by `Components`'s `mergeStep`/`buildComponents`: an
incremental union-find over `Finset V` partitions, processing each edge's
own two endpoints once and merging any existing components they touch —
no `Finset.univ` scan, no BFS rounds, no walk enumeration, and (per the
subtlety above) no `Classical.choice`-requiring endpoint-naming either,
since it operates on `edgeVerts`-derived `Finset`s rather than named
vertices throughout. `decidableIsForestInsertOfList` now delegates to
`decidableIsForestInsertOfComponents` (building a fresh `forestComponents`
each call), and `instDecidableIsForestOfList`'s own recursive `O(|l|)`-many
calls benefit the same way — this dropped `nested`'s `verify_cert` from
~26s to ~2.5s and its `native_decide`-based end-to-end test from ~300s to
~10s. An array-backed union-find (`Batteries.UnionFind`) was considered and
rejected before settling on this `Finset`-based version: indexing into it
needs a computable `V ≃ Fin (card V)` bijection, which is noncomputable in
Mathlib for a bare `[Fintype V]` (extracting a canonical enumeration from
an abstract `Finset`'s underlying `Multiset` quotient needs choice) — the
same computability obstruction the file's design has to avoid throughout.

**Main results:**
- `isForest_insert_iff`: given `F` is already a forest, inserting a new edge
  `e` (with endpoints `u ≠ v`) keeps it a forest iff `u`, `v` weren't already
  reachable in `F`'s simple graph. Both directions — the forward direction is
  Mathlib's own edge-addition acyclicity iff, transported through
  `Multigraph.toSimpleGraph`; the backward direction is exactly
  `Multigraph.IsForest.insert_of_not_reachable`, already proved upstream.
- `instDecidableIsForestOfList`: a genuine, `decide`-reducible
  `Decidable (G.IsForest {e | e ∈ l})` instance for any `l : List E`, given
  `Fintype V`, `DecidableEq V`, `DecidableEq E` — exactly the concrete-graph
  setting a certificate parser runs in, and exactly the shape (an edge-index
  list) a certificate's declared tree already comes in.
-/

namespace DiscreteModulusCert

open Multigraph

variable {V E : Type*} (G : Multigraph V E)

section Adjacency

variable [DecidableEq V]

/-- `toSimpleGraph`'s adjacency relation is decidable for a `List` edge set:
`u`/`v` are adjacent iff some edge of `l` realizes the pair `s(u, v)`, a
finite search over `l`. -/
instance instDecidableRelAdjToSimpleGraphOfList (l : List E) :
    DecidableRel (G.toSimpleGraph {e | e ∈ l}).Adj := fun u v => by
  have himg : (G.endpoints '' {e | e ∈ l} : Set (Sym2 V)) = {z | z ∈ l.map G.endpoints} := by
    ext z; simp [Set.mem_image]
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj, himg]
  infer_instance

end Adjacency

section InsertIff

variable {F : Set E} {e : E} {u v : V}

/-- **The insertion step of the decision procedure.** Given `F` is already a
forest and a new edge `e` (not in `F`, with endpoints `u ≠ v`), `insert e F`
is a forest iff `u` and `v` weren't already reachable in `F`'s simple graph.
The `mpr` direction is exactly `IsForest.insert_of_not_reachable` (already
proved in `lean-modulus`'s `Multigraph.lean`); the `mp` direction is new here,
obtained by rewriting `toSimpleGraph (insert e F)` as `toSimpleGraph F ⊔ edge
u v` and invoking Mathlib's `isAcyclic_sup_fromEdgeSet_iff`, whose `Reachable
u v → u = v ∨ Adj u v` conclusion collapses to `¬ Reachable u v` once `u ≠ v`
and `e`'s endpoints aren't already realized in `F` (itself forced by
`insert e F`'s own injectivity-on-endpoints conjunct). -/
theorem isForest_insert_iff (hF : G.IsForest F) (heF : e ∉ F)
    (huv : G.endpoints e = s(u, v)) (hne : u ≠ v) :
    G.IsForest (insert e F) ↔ ¬ (G.toSimpleGraph F).Reachable u v := by
  have hsup : G.toSimpleGraph (insert e F) = G.toSimpleGraph F ⊔ SimpleGraph.edge u v := by
    rw [Multigraph.toSimpleGraph, Multigraph.toSimpleGraph, Set.image_insert_eq, huv,
      Set.insert_eq, SimpleGraph.fromEdgeSet_union]
    exact sup_comm (SimpleGraph.fromEdgeSet {s(u, v)}) (SimpleGraph.fromEdgeSet (G.endpoints '' F))
  constructor
  · rintro ⟨-, hinj, hacyc⟩ hreach
    rw [hsup, SimpleGraph.isAcyclic_sup_fromEdgeSet_iff] at hacyc
    rcases hacyc.2 hreach with h | h
    · exact hne h
    · rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at h
      obtain ⟨⟨b, hbF, hbe⟩, -⟩ := h
      have hbeq : b = e := hinj (Set.mem_insert_of_mem e hbF) (Set.mem_insert e F)
        (hbe.trans huv.symm)
      exact heF (hbeq ▸ hbF)
  · exact Multigraph.IsForest.insert_of_not_reachable G hF heF huv hne

end InsertIff

section Components

private theorem coe_setOf_mem_cons (a : E) (l : List E) :
    ({e | e ∈ (a :: l)} : Set E) = insert a {e | e ∈ l} := by
  ext x; simp [List.mem_cons]

private theorem coe_setOf_mem_cons_of_mem {a : E} {l : List E} (ha : a ∈ l) :
    ({e | e ∈ (a :: l)} : Set E) = {e | e ∈ l} := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_cons]
  exact ⟨fun h => h.elim (fun h => h ▸ ha) id, Or.inr⟩

/-!
**A components cache, for callers checking many candidate insertions
against the same base forest.** A certificate's maximality check
(`CertChecker.lean`'s `checkTree`) calls a single-insertion decision once
per candidate edge, `O(|piece edges|)` candidates against the *same* base
forest. `forestComponents` below computes that graph's connected
components *once* via `mergeStep`/`buildComponents` (an incremental
union-find over `Finset V` partitions — see the file docstring for why
this replaced an earlier `bfsClosure`-based version), so repeated queries
against the shared cache become cheap `Finset`/`List` lookups instead of
each candidate redoing its own reachability search.
`decidableIsForestInsertOfList` (`Decide` below) reuses this same
components cache, building it fresh per call since it has no precomputed
cache of its own to share across calls the way the maximality-check loop
does.
-/

variable [Fintype V] [DecidableEq V]

/-- The (at most 2-element) vertex set of a `Sym2 V` edge value, extracted
without ever naming which vertex is "first" — swap-invariance here is the
trivial fact `{u, v} = {v, u}` as `Finset`s, unlike trying to extract an
*ordered* pair (which would need extra structure on `V` to pick a
canonical order, unavailable for a bare `[Fintype V] [DecidableEq V]`). -/
def edgeVerts (z : Sym2 V) : Finset V :=
  Sym2.lift ⟨fun u v => ({u, v} : Finset V), fun u v => by
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩ z

omit [Fintype V] in
theorem edgeVerts_mk (u v : V) : edgeVerts (s(u, v) : Sym2 V) = ({u, v} : Finset V) := rfl

/-- Whether `p`/`q` lie in a common component of a partition `P` — `p = q`
covers vertices untouched by any component (implicitly their own singleton
component). -/
def connected (P : List (Finset V)) (p q : V) : Prop :=
  p = q ∨ ∃ c ∈ P, p ∈ c ∧ q ∈ c

instance decConnected (P : List (Finset V)) (p q : V) : Decidable (connected P p q) := by
  unfold connected; infer_instance

/-- Two `Finset`s recorded in the partition never share a vertex — the
invariant that makes `connected` (below) genuinely transitive, and that
`buildComponents`'s incremental merging maintains throughout. -/
def PairwiseDisjointFinsets (P : List (Finset V)) : Prop := P.Pairwise Disjoint

omit [Fintype V] in
theorem disjoint_foldl_union (l : List (Finset V)) (init c : Finset V)
    (hinit : Disjoint init c) (hl : ∀ o ∈ l, Disjoint o c) :
    Disjoint (l.foldl (· ∪ ·) init) c := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact Finset.disjoint_union_left.mpr ⟨hinit, hl hd List.mem_cons_self⟩
    · intro o ho
      exact hl o (List.mem_cons_of_mem hd ho)

/-- **Merge `verts` into the partition `P`.** Absorb every existing
component that shares a vertex with `verts` into one new component (union
them all together with `verts` itself); components disjoint from `verts`
pass through unchanged. Unlike the old `bfsClosure`-based version, this
never scans `Finset.univ` (the *whole* graph's vertex `Fintype`) — it only
ever touches vertices that already appear in `verts` or an already-recorded
component. Confirmed to matter: on `nested.certificate.json` (60 vertices
total, but any one piece touches only ~20 of them), `bfsStep`'s per-round
`Finset.univ.filter` scan, combined with `instDecidableRelAdjToSimpleGraphOfList`'s
own per-vertex edge-list scan, was the dominant cost of `verify_cert`
(confirmed via `perf`: ~57% of cycles in the adjacency-check path) — this
union-based merge sidesteps `Finset.univ` (and `bfsStep`/`bfsClosure`
entirely) for the components cache, processing each edge exactly once. -/
def mergeStep (verts : Finset V) (P : List (Finset V)) : List (Finset V) :=
  let overlap := P.filter (fun c => ¬ Disjoint verts c)
  let rest := P.filter (fun c => Disjoint verts c)
  (overlap.foldl (· ∪ ·) verts) :: rest

omit [Fintype V] in
theorem pairwiseDisjoint_mergeStep (verts : Finset V) (P : List (Finset V))
    (hP : PairwiseDisjointFinsets P) : PairwiseDisjointFinsets (mergeStep verts P) := by
  unfold PairwiseDisjointFinsets mergeStep
  rw [List.pairwise_cons]
  constructor
  · intro c hc
    have hcP : c ∈ P := (List.mem_filter.mp hc).1
    have hcDisj : Disjoint verts c := of_decide_eq_true (List.mem_filter.mp hc).2
    apply disjoint_foldl_union
    · exact hcDisj
    · intro o ho
      have hoP : o ∈ P := (List.mem_filter.mp ho).1
      have hoNotDisj : ¬ Disjoint verts o := of_decide_eq_true (List.mem_filter.mp ho).2
      have hne : o ≠ c := fun h => hoNotDisj (h ▸ hcDisj)
      exact hP.forall hoP hcP hne
  · exact List.Pairwise.sublist List.filter_sublist hP

omit [Fintype V] in
theorem reachable_union_of_not_disjoint (H : SimpleGraph V) [DecidableRel H.Adj]
    {A B : Finset V} (hA : ∀ p ∈ A, ∀ q ∈ A, H.Reachable p q)
    (hB : ∀ p ∈ B, ∀ q ∈ B, H.Reachable p q) (hAB : ¬ Disjoint A B) :
    ∀ p ∈ A ∪ B, ∀ q ∈ A ∪ B, H.Reachable p q := by
  obtain ⟨w, hwA, hwB⟩ := Finset.not_disjoint_iff.mp hAB
  intro p hp q hq
  simp only [Finset.mem_union] at hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hA p hp q hq
  · exact (hA p hp w hwA).trans (hB w hwB q hq)
  · exact (hB p hp w hwB).trans (hA w hwA q hq)
  · exact hB p hp q hq

omit [Fintype V] in
theorem reachable_foldl_union (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (overlap : List (Finset V)) (verts : Finset V),
    (∀ o ∈ overlap, ¬ Disjoint verts o) →
    (∀ o ∈ overlap, ∀ p ∈ o, ∀ q ∈ o, H.Reachable p q) →
    (∀ p ∈ verts, ∀ q ∈ verts, H.Reachable p q) →
    ∀ p ∈ overlap.foldl (· ∪ ·) verts, ∀ q ∈ overlap.foldl (· ∪ ·) verts, H.Reachable p q
  | [], verts, _, _, hvertsReach => by simpa using hvertsReach
  | hd :: tl, verts, hoverlap, hvalid, hvertsReach => by
      simp only [List.foldl_cons]
      apply reachable_foldl_union H tl (verts ∪ hd)
      · intro o ho hcontra
        exact hoverlap o (List.mem_cons_of_mem hd ho)
          (hcontra.mono_left Finset.subset_union_left)
      · intro o ho
        exact hvalid o (List.mem_cons_of_mem hd ho)
      · exact reachable_union_of_not_disjoint H hvertsReach
          (hvalid hd List.mem_cons_self) (hoverlap hd List.mem_cons_self)

/-- Every component recorded so far is internally mutually `H`-reachable —
the soundness half of the partition invariant `buildComponents` maintains
(true, in `forestComponents` below, of a seed formed from a single edge's
own two endpoints). -/
def ValidComponents (H : SimpleGraph V) [DecidableRel H.Adj] (P : List (Finset V)) : Prop :=
  ∀ c ∈ P, ∀ p ∈ c, ∀ q ∈ c, H.Reachable p q

omit [Fintype V] in
theorem validComponents_mergeStep (H : SimpleGraph V) [DecidableRel H.Adj]
    (verts : Finset V) (P : List (Finset V))
    (hverts : ∀ p ∈ verts, ∀ q ∈ verts, H.Reachable p q)
    (hP : ValidComponents H P) : ValidComponents H (mergeStep verts P) := by
  unfold ValidComponents mergeStep
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · apply reachable_foldl_union H _ verts
    · intro o ho
      exact of_decide_eq_true (List.mem_filter.mp ho).2
    · intro o ho
      exact hP o (List.mem_filter.mp ho).1
    · exact hverts
  · exact hP c (List.mem_filter.mp hc).1

/-- **Building the partition by folding `mergeStep` over a list of edge
seeds.** Replaces the old `bfsClosure`-per-new-component version: no
`bfsStep`/`Finset.univ` scanning anywhere in this construction, since
`mergeStep` only ever touches vertices already present in `verts` or an
existing component. -/
def buildComponents : List (Finset V) → List (Finset V) → List (Finset V)
  | [], P => P
  | verts :: rest, P => buildComponents rest (mergeStep verts P)

omit [Fintype V] in
theorem pairwiseDisjoint_buildComponents :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)), PairwiseDisjointFinsets P →
      PairwiseDisjointFinsets (buildComponents seeds P)
  | [], _, hP => hP
  | _ :: rest, P, hP =>
      pairwiseDisjoint_buildComponents rest _ (pairwiseDisjoint_mergeStep _ P hP)

omit [Fintype V] in
theorem validComponents_buildComponents (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)),
      (∀ verts ∈ seeds, ∀ p ∈ verts, ∀ q ∈ verts, H.Reachable p q) →
      ValidComponents H P → ValidComponents H (buildComponents seeds P)
  | [], _, _, hP => hP
  | verts :: rest, P, hseeds, hP =>
      validComponents_buildComponents H rest _
        (fun v hv => hseeds v (List.mem_cons_of_mem _ hv))
        (validComponents_mergeStep H verts P (hseeds verts List.mem_cons_self) hP)

omit [Fintype V] in
theorem connected_trans {P : List (Finset V)} (hP : PairwiseDisjointFinsets P)
    {p q r : V} (hpq : connected P p q) (hqr : connected P q r) : connected P p r := by
  rcases hpq with rfl | ⟨c1, hc1, hpc1, hqc1⟩
  · exact hqr
  rcases hqr with rfl | ⟨c2, hc2, hqc2, hrc2⟩
  · exact Or.inr ⟨c1, hc1, hpc1, hqc1⟩
  by_cases heq : c1 = c2
  · exact Or.inr ⟨c1, hc1, hpc1, heq ▸ hrc2⟩
  · exact absurd hqc2 (Finset.disjoint_left.mp (hP.forall hc1 hc2 heq) hqc1)

omit [Fintype V] in
theorem subset_foldl_union_self (l : List (Finset V)) (init : Finset V) :
    init ⊆ l.foldl (· ∪ ·) init := by
  induction l generalizing init with
  | nil => exact subset_rfl
  | cons hd tl ih => exact Finset.subset_union_left.trans (ih (init ∪ hd))

omit [Fintype V] in
theorem mem_foldl_union_of_mem_init (l : List (Finset V)) (init : Finset V) {x : V}
    (hx : x ∈ init) : x ∈ l.foldl (· ∪ ·) init :=
  subset_foldl_union_self l init hx

omit [Fintype V] in
theorem mem_foldl_union_of_mem_list :
    ∀ (l : List (Finset V)) (init : Finset V) (o : Finset V), o ∈ l → ∀ x ∈ o,
      x ∈ l.foldl (· ∪ ·) init
  | hd :: tl, init, o, ho, x, hx => by
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp ho with rfl | ho'
      · exact mem_foldl_union_of_mem_init tl (init ∪ o) (Finset.mem_union_right init hx)
      · exact mem_foldl_union_of_mem_list tl (init ∪ hd) o ho' x hx

omit [Fintype V] in
theorem connected_mergeStep_of_connected {P : List (Finset V)} (verts : Finset V) {p q : V}
    (h : connected P p q) : connected (mergeStep verts P) p q := by
  rcases h with rfl | ⟨c, hc, hpc, hqc⟩
  · exact Or.inl rfl
  · unfold mergeStep
    by_cases hcd : Disjoint verts c
    · exact Or.inr ⟨c, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, decide_eq_true hcd⟩),
        hpc, hqc⟩
    · refine Or.inr ⟨(P.filter (fun c => ¬ Disjoint verts c)).foldl (· ∪ ·) verts,
        List.mem_cons_self, ?_, ?_⟩
      · exact mem_foldl_union_of_mem_list _ verts c
          (List.mem_filter.mpr ⟨hc, decide_eq_true hcd⟩) p hpc
      · exact mem_foldl_union_of_mem_list _ verts c
          (List.mem_filter.mpr ⟨hc, decide_eq_true hcd⟩) q hqc

omit [Fintype V] in
theorem connected_buildComponents_of_connected :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)) {p q : V}, connected P p q →
      connected (buildComponents seeds P) p q
  | [], _, _, _, h => h
  | verts :: rest, _, _, _, h =>
      connected_buildComponents_of_connected rest _ (connected_mergeStep_of_connected verts h)

omit [Fintype V] in
theorem connected_of_mem_seed :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)) (verts : Finset V), verts ∈ seeds →
      ∀ p ∈ verts, ∀ q ∈ verts, connected (buildComponents seeds P) p q
  | v :: rest, P, verts, hverts, p, hp, q, hq => by
      rcases List.mem_cons.mp hverts with rfl | hverts'
      · unfold buildComponents
        apply connected_buildComponents_of_connected
        unfold mergeStep
        exact Or.inr ⟨_, List.mem_cons_self,
          subset_foldl_union_self _ verts hp, subset_foldl_union_self _ verts hq⟩
      · unfold buildComponents
        exact connected_of_mem_seed rest (mergeStep v P) verts hverts' p hp q hq

variable [DecidableEq E]

/-- The connected-components cache of `{e | e ∈ l}`'s own simple graph:
fold over `l`'s edges (as `edgeVerts` seeds), merging into a component
partition as described above. -/
def forestComponents (l : List E) : List (Finset V) :=
  buildComponents (l.map (fun e => edgeVerts (G.endpoints e))) []

omit [Fintype V] [DecidableEq E] in
theorem mem_edgeVerts_reachable (l : List E) {e : E} (he : e ∈ l) :
    ∀ p ∈ edgeVerts (G.endpoints e), ∀ q ∈ edgeVerts (G.endpoints e),
      (G.toSimpleGraph {e' | e' ∈ l}).Reachable p q := by
  obtain ⟨a, b, hab⟩ := Sym2.exists.mp ⟨G.endpoints e, rfl⟩
  rw [hab, edgeVerts_mk]
  intro p hp q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  by_cases heq : a = b
  · subst heq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> exact SimpleGraph.Reachable.refl _
  · have hadj : (G.toSimpleGraph {e' | e' ∈ l}).Adj a b := by
      rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨e, he, hab⟩, heq⟩
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
    · exact hadj.symm.reachable
    · exact SimpleGraph.Reachable.refl _

omit [DecidableEq E] in
omit [Fintype V] in
theorem validComponents_forestComponents (l : List E) :
    ValidComponents (G.toSimpleGraph {e | e ∈ l}) (forestComponents G l) :=
  validComponents_buildComponents _ _ _
    (fun verts hv => by
      simp only [List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv
      exact mem_edgeVerts_reachable G l he)
    (fun c hc => absurd hc (List.not_mem_nil))

omit [DecidableEq E] in
omit [Fintype V] in
theorem connected_of_mem_edge (l : List E) {e : E} (he : e ∈ l) :
    ∀ p ∈ edgeVerts (G.endpoints e), ∀ q ∈ edgeVerts (G.endpoints e),
      connected (forestComponents G l) p q :=
  connected_of_mem_seed (l.map (fun e' => edgeVerts (G.endpoints e'))) []
    (edgeVerts (G.endpoints e)) (List.mem_map.mpr ⟨e, he, rfl⟩)

omit [DecidableEq E] in
omit [Fintype V] in
theorem reachable_imp_connected (l : List E) {p q : V}
    (w : (G.toSimpleGraph {e | e ∈ l}).Walk p q) : connected (forestComponents G l) p q := by
  induction w with
  | nil => exact Or.inl rfl
  | @cons p x _ hadj rest ih =>
      obtain ⟨e, he, heq⟩ : ∃ e ∈ l, G.endpoints e = s(p, x) := by
        rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hadj
        obtain ⟨⟨e, he, heq⟩, -⟩ := hadj
        exact ⟨e, he, heq⟩
      have hpx : connected (forestComponents G l) p x := by
        have hp : p ∈ edgeVerts (G.endpoints e) := by rw [heq, edgeVerts_mk]; simp
        have hx : x ∈ edgeVerts (G.endpoints e) := by rw [heq, edgeVerts_mk]; simp
        exact connected_of_mem_edge G l he p hp x hx
      have hdisj : PairwiseDisjointFinsets (forestComponents G l) :=
        pairwiseDisjoint_buildComponents _ [] List.Pairwise.nil
      exact connected_trans hdisj hpx ih

omit [DecidableEq E] [Fintype V] in
/-- **Correctness of the components cache.** `p`/`q` lie in a common
component of `forestComponents G l` iff they're reachable in `l`'s own
simple graph. Soundness is direct from `ValidComponents`; completeness
peels a `p`–`q` walk apart one edge at a time (`reachable_imp_connected`),
placing each step's own two endpoints together via `connected_of_mem_edge`
and chaining across steps via `connected_trans`. -/
theorem connected_forestComponents_iff (l : List E) (p q : V) :
    connected (forestComponents G l) p q ↔ (G.toSimpleGraph {e | e ∈ l}).Reachable p q := by
  have hvalid := validComponents_forestComponents G l
  constructor
  · rintro (rfl | ⟨c, hc, hpc, hqc⟩)
    · exact SimpleGraph.Reachable.refl p
    · exact hvalid c hc p hpc q hqc
  · rintro ⟨w⟩
    exact reachable_imp_connected G l w

/-- **The single-insertion decision, backed by a components cache.** Same
statement as `decidableIsForestInsertOfList` (which is in fact a thin
wrapper around this, below), but takes the components cache (`comps`,
assumed to already be `forestComponents G l`) as a parameter rather than
building it itself — the version to call from a loop testing many
candidate insertions against the same base forest, so the cache is built
once and reused across all of them instead of once per candidate. -/
def decidableIsForestInsertOfComponents (l : List E) (a : E)
    (hF : G.IsForest ({e | e ∈ l} : Set E)) (comps : List (Finset V))
    (hcomps : comps = forestComponents G l) :
    Decidable (G.IsForest ({e | e ∈ (a :: l)} : Set E)) :=
  if ha : a ∈ l then
    isTrue (by rw [coe_setOf_mem_cons_of_mem ha]; exact hF)
  else if hloop : (G.endpoints a).IsDiag then
    isFalse (fun hFs => (hFs.1 a (by
      rw [coe_setOf_mem_cons]; exact Set.mem_insert a _)) hloop)
  else if hreach : ∃ c ∈ comps, edgeVerts (G.endpoints a) ⊆ c then
    isFalse (fun hFs => by
      induction huv : G.endpoints a with
      | _ u v =>
      have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
      have hFs' : G.IsForest (insert a ({e | e ∈ l} : Set E)) := by
        rw [← coe_setOf_mem_cons]; exact hFs
      have hreach' : (G.toSimpleGraph {e | e ∈ l}).Reachable u v := by
        rw [← connected_forestComponents_iff, ← hcomps]
        obtain ⟨c, hc, hsub⟩ := hreach
        refine Or.inr ⟨c, hc, hsub ?_, hsub ?_⟩ <;> rw [huv, edgeVerts_mk] <;> simp
      exact (isForest_insert_iff G hF ha huv hne).mp hFs' hreach')
  else
    isTrue (by
      induction huv : G.endpoints a with
      | _ u v =>
      have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
      have hnr : ¬ (G.toSimpleGraph {e | e ∈ l}).Reachable u v := fun hcontra => by
        apply hreach
        rw [hcomps]
        rcases (connected_forestComponents_iff G l u v).mpr hcontra with h | ⟨c, hc, hu, hv⟩
        · exact absurd h hne
        · refine ⟨c, hc, ?_⟩
          rw [huv, edgeVerts_mk]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hu
          · exact hv
      rw [coe_setOf_mem_cons]
      exact (isForest_insert_iff G hF ha huv hne).mpr hnr)

end Components

section Decide

variable [Fintype V] [DecidableEq V] [DecidableEq E]

/-- **The single-insertion decision, reusable against a fixed base forest.**
Given `{e' | e' ∈ l}` is already known to be a forest, decide whether
`insert a {e' | e' ∈ l}` still is. A thin wrapper around
`decidableIsForestInsertOfComponents`, building `forestComponents G l`
fresh each call -- there's no cache to reuse here (unlike a maximality
check's loop over many candidates against one base forest), but this still
avoids the old `bfsClosure`/`Finset.univ`-scanning path entirely, which is
what `instDecidableIsForestOfList`'s own `O(|l|)`-many per-level calls
(once per recursion level, each checking a different growing prefix)
actually bottlenecked on -- confirmed via `perf` to dominate real
`verify_cert` runtime even after `decidableIsForestInsertOfComponents`'s
own maximality-check path was fixed the same way. -/
def decidableIsForestInsertOfList (l : List E) (a : E) (hF : G.IsForest ({e | e ∈ l} : Set E)) :
    Decidable (G.IsForest ({e | e ∈ (a :: l)} : Set E)) :=
  decidableIsForestInsertOfComponents G l a hF (forestComponents G l) rfl

/-- **The decision procedure itself.** Structural recursion on `l : List E`:
`[]` is trivially a forest; for `a :: rest`, decide `G.IsForest {e | e ∈ rest}`
recursively, and if that holds, hand off to `decidableIsForestInsertOfList`
for the single insertion step. -/
instance instDecidableIsForestOfList :
    ∀ l : List E, Decidable (G.IsForest ({e | e ∈ l} : Set E))
  | [] => isTrue (by
      have hempty : ({e | e ∈ ([] : List E)} : Set E) = ∅ := by ext x; simp
      rw [hempty]
      exact ⟨fun e he => absurd he (Set.notMem_empty e), Set.injOn_empty _, by
        rw [Multigraph.toSimpleGraph, Set.image_empty, SimpleGraph.fromEdgeSet_empty]
        exact SimpleGraph.isAcyclic_bot⟩)
  | a :: rest =>
      match instDecidableIsForestOfList rest with
      | isFalse hns =>
          isFalse (fun hFs => hns (Multigraph.IsForest.subset G hFs (by
            rw [coe_setOf_mem_cons]; exact Set.subset_insert a _)))
      | isTrue hF => decidableIsForestInsertOfList G rest a hF

end Decide

end DiscreteModulusCert
