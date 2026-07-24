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
  `sym2Reachable` lifts `Reachable` through `Sym2.lift` (valid since
  reachability is symmetric) so that "are this edge's endpoints already
  connected" is decidable *at the `Sym2 V` value itself*, via
  `Quot.recOnSubsingleton` (`Decidable` is a subsingleton up to proof
  irrelevance, so eliminating the quotient to select a `Decidable` value is
  legitimate, and the kernel's `Quot` computation rule still fires
  definitionally on any literal `s(u, v)` — exactly what a concrete
  certificate provides). Naming the endpoints is then only ever needed
  *inside* the resulting proof obligations (`Prop`-to-`Prop` elimination,
  always fine), never to pick the `Decidable` branch.

Both fixes were confirmed necessary and sufficient by direct experiment
(`#eval`/`decide` on a 3-cycle test graph) before settling on this design.

**Performance fix (the exponential blowup).** The design above type-checks
and is correct at any size, but was originally wired to Mathlib's own
`DecidableRel Reachable` instance for "are these endpoints already
connected" — which turned out to be a genuine algorithmic trap, not just a
kernel-reduction inconvenience: it's built by transporting decidability
across `reachable_iff_exists_finsetWalkLength_nonempty`, whose witness
search (`finsetWalkLength`) enumerates *every walk* of each candidate
length by branching over every neighbor at every step, no visited-set
pruning at all — exponential in `Fintype.card V`, confirmed directly to
hang for minutes on a 190-edge/20-vertex nearly-complete piece even under
`native_decide` (compiled code, so not a `decide`-vs-`native_decide`
reduction-strategy artifact — a genuinely exponential computation however
it's run). `FastReachable` below replaces it with a textbook bounded BFS
closure over plain `Finset` operations — polynomial, not exponential — and
`decSym2Reachable` is wired to use it instead of `infer_instance` (which
would otherwise silently keep picking up Mathlib's exponential instance).
See `FastReachable`'s own section docstring for why this is a `Finset`-BFS
rather than an array-backed union-find (the natural first choice, ruled
out by a real computability obstruction).

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

section FastReachable

variable [Fintype V] [DecidableEq V]

/-- **The efficient replacement for Mathlib's `Reachable` decidability.**
Mathlib's own `DecidableRel Reachable` instance
(`SimpleGraph.instDecidableRelReachable`, `Connectivity/Finite.lean`) is
transported across `reachable_iff_exists_finsetWalkLength_nonempty`, whose
witness search (`finsetWalkLength`) *literally enumerates every walk* of
each candidate length by branching over every neighbor at every step, with
no visited-set pruning — genuinely exponential in `Fintype.card V` for any
graph with vertices of degree ≥ 2, not merely slow-to-kernel-reduce. On a
190-edge/20-vertex nearly-complete piece (`nested.certificate.json`'s
piece 0) this is why `instDecidableIsForestOfList` used to hang for
minutes even under `native_decide` (compiled code, not kernel reduction —
confirmed by direct experiment that the blowup is algorithmic, not a
reduction-strategy artifact).

The fix: a textbook bounded BFS closure (`bfsStep`/`bfsClosure` below),
computed with ordinary `Finset` operations over `Fintype V` — no
`Fin`-indexed array structure needed (an array/union-find-based fix was
considered and rejected: `Fintype.equivFin`, the standard `V ≃ Fin
(card V)` embedding needed to key into an efficient array-backed
disjoint-set structure like `Batteries.UnionFind`, is `noncomputable` in
Mathlib for a bare `[Fintype V]` — extracting a canonical enumeration from
an abstract `Finset`'s underlying `Multiset` quotient needs choice, exactly
the kind of noncomputability this file has to avoid throughout). Cost is
`O(|V|)` rounds × `O(|V|)` frontier vertices × `O(|F|)` per adjacency query
(`instDecidableRelAdjToSimpleGraphOfList` scans the edge list) —
polynomial, not exponential, and easily fast enough at the ~200-edge/
~20-vertex scale a certificate piece actually needs (confirmed directly:
seconds, not minutes, on `nested`/`branch_test`'s worst pieces). -/
def bfsStep (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : Finset V :=
  S ∪ S.biUnion fun u => Finset.univ.filter (H.Adj u)

theorem subset_bfsStep (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) :
    S ⊆ bfsStep H S :=
  Finset.subset_union_left

/-- Whenever a round of `bfsStep` still changes something, it strictly grows
`S`'s cardinality — the fact that lets `bfsClosure` below terminate by
running rounds only until it actually stops changing (a genuine fixed
point), rather than a fixed `Fintype.card V` rounds regardless of how
quickly the graph in question actually stabilizes. This is what turns the
`Fintype.card V`-vertex factor from a *guaranteed* multiplier (paid even
when the relevant piece is tiny and the closure stabilizes in a handful of
rounds) into a mere worst-case bound. -/
theorem bfsStep_card_lt_of_ne (H : SimpleGraph V) [DecidableRel H.Adj] {S : Finset V}
    (h : bfsStep H S ≠ S) :
    Fintype.card V - (bfsStep H S).card < Fintype.card V - S.card := by
  have hlt : S.card < (bfsStep H S).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_bfsStep H S, Ne.symm h⟩)
  have hle : (bfsStep H S).card ≤ Fintype.card V := by
    simpa using Finset.card_le_univ (bfsStep H S)
  omega

/-- **BFS closure of `S` under `H`-adjacency, stopping as soon as a round adds
nothing new** — a genuine fixed point of `bfsStep`, computed by well-founded
recursion on `Fintype.card V - S.card` (terminates: `bfsStep_card_lt_of_ne`).
Unlike a fixed `Fintype.card V`-round version, this pays for extra rounds
only when the graph in question actually needs them, instead of always
paying a `Fintype.card V` multiplier even on a tiny/sparse piece — the
difference between finishing in seconds and taking minutes on a real
certificate's per-candidate maximality checks (each one a fresh reachability
query against an already-small forest). -/
def bfsClosure (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : Finset V :=
  if h : bfsStep H S = S then S
  else
    have := bfsStep_card_lt_of_ne H h
    bfsClosure H (bfsStep H S)
termination_by Fintype.card V - S.card

theorem subset_bfsClosure (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ S : Finset V, S ⊆ bfsClosure H S
  | S => by
    unfold bfsClosure
    split
    · next h => exact subset_rfl
    · next h =>
      have := bfsStep_card_lt_of_ne H h
      exact (subset_bfsStep H S).trans (subset_bfsClosure H (bfsStep H S))
termination_by S => Fintype.card V - S.card

/-- `bfsClosure` really is a fixed point of `bfsStep` — the fact that lets
`reachable_iff_mem_bfsClosure` below invoke `SimpleGraph.reachable_le_of_adj_le`
directly, rather than needing an explicit walk-length bound. -/
theorem bfsClosure_fixedPoint (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ S : Finset V, bfsStep H (bfsClosure H S) = bfsClosure H S
  | S => by
    unfold bfsClosure
    split
    · next h => exact h
    · next h =>
      have := bfsStep_card_lt_of_ne H h
      exact bfsClosure_fixedPoint H (bfsStep H S)
termination_by S => Fintype.card V - S.card

/-- A fixed point of `bfsStep` is closed under one `H`-adjacency hop. -/
theorem mem_bfsClosure_of_adj (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) {p q : V}
    (hp : p ∈ bfsClosure H S) (hpq : H.Adj p q) : q ∈ bfsClosure H S := by
  rw [← bfsClosure_fixedPoint H S]
  simp only [bfsStep, Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩⟩

/-- Conversely, every vertex in a BFS closure of a set of already-reachable
vertices is itself reachable — by well-founded induction mirroring
`bfsClosure`'s own recursion, since `bfsStep` only ever adds direct
neighbors of already-included (hence already-reachable) vertices. -/
theorem reachable_of_mem_bfsClosure (H : SimpleGraph V) [DecidableRel H.Adj] {u : V} :
    ∀ {S : Finset V}, (∀ x ∈ S, H.Reachable u x) → ∀ {y}, y ∈ bfsClosure H S → H.Reachable u y
  | S, hS, y, hy => by
    unfold bfsClosure at hy
    split at hy
    · next h => exact hS y hy
    · next h =>
      have := bfsStep_card_lt_of_ne H h
      refine reachable_of_mem_bfsClosure H (S := bfsStep H S) (fun x hx => ?_) hy
      simp only [bfsStep, Finset.mem_union, Finset.mem_biUnion] at hx
      rcases hx with hx | ⟨s, hsS, hsx⟩
      · exact hS x hx
      · exact (hS s hsS).trans (Finset.mem_filter.mp hsx).2.reachable
termination_by S => Fintype.card V - S.card

/-- **Correctness of the fast reachability check.** `v` lies in `u`'s BFS
closure iff `u` and `v` are `H`-reachable. The "only if" direction is
`SimpleGraph.reachable_le_of_adj_le` (`Reachable` is the *smallest*
reflexive-transitive relation containing `Adj`) applied to
`fun p q => p ∈ bfsClosure H {u} → q ∈ bfsClosure H {u}`, whose `Adj`-closure
is exactly `mem_bfsClosure_of_adj`. -/
theorem reachable_iff_mem_bfsClosure (H : SimpleGraph V) [DecidableRel H.Adj] (u v : V) :
    H.Reachable u v ↔ v ∈ bfsClosure H ({u} : Finset V) := by
  constructor
  · intro hreach
    have hmem : u ∈ bfsClosure H ({u} : Finset V) :=
      subset_bfsClosure H _ (Finset.mem_singleton_self u)
    exact SimpleGraph.reachable_le_of_adj_le (fun _ h => h)
      (fun _ _ _ h1 h2 h3 => h2 (h1 h3))
      (fun p q hpq h => mem_bfsClosure_of_adj H _ h hpq) u v hreach hmem
  · exact reachable_of_mem_bfsClosure H
      (fun x hx => by rw [Finset.mem_singleton.mp hx])

/-- Generalization of `reachable_iff_mem_bfsClosure` to a `Finset` of seed
vertices at once: `q` lies in `S`'s BFS closure iff it's `H`-reachable from
*some* element of `S`. Lets `Components` below compute a whole connected
component from a single (2-vertex, edge-shaped) seed in one `bfsClosure`
call. -/
theorem exists_reachable_of_mem_bfsClosure (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ {S : Finset V} {q : V}, q ∈ bfsClosure H S → ∃ p ∈ S, H.Reachable p q
  | S, q, hq => by
    unfold bfsClosure at hq
    split at hq
    · next h => exact ⟨q, hq, SimpleGraph.Reachable.refl q⟩
    · next h =>
      have := bfsStep_card_lt_of_ne H h
      obtain ⟨p, hp, hpq⟩ := exists_reachable_of_mem_bfsClosure H (S := bfsStep H S) hq
      simp only [bfsStep, Finset.mem_union, Finset.mem_biUnion] at hp
      rcases hp with hp | ⟨s, hsS, hsp⟩
      · exact ⟨p, hp, hpq⟩
      · exact ⟨s, hsS, (Finset.mem_filter.mp hsp).2.reachable.trans hpq⟩
termination_by S => Fintype.card V - S.card

theorem mem_bfsClosure_of_reachable (H : SimpleGraph V) [DecidableRel H.Adj] {S : Finset V}
    {p q : V} (hpS : p ∈ S) (hpq : H.Reachable p q) : q ∈ bfsClosure H S := by
  have hmem : p ∈ bfsClosure H S := subset_bfsClosure H S hpS
  exact SimpleGraph.reachable_le_of_adj_le (fun _ h => h)
    (fun _ _ _ h1 h2 h3 => h2 (h1 h3))
    (fun x y hxy h => mem_bfsClosure_of_adj H _ h hxy) p q hpq hmem

theorem mem_bfsClosure_iff (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (q : V) :
    q ∈ bfsClosure H S ↔ ∃ p ∈ S, H.Reachable p q :=
  ⟨exists_reachable_of_mem_bfsClosure H, fun ⟨_, hpS, hpq⟩ => mem_bfsClosure_of_reachable H hpS hpq⟩

end FastReachable

section ReachableOnSym2

variable [Fintype V] [DecidableEq V]

/-- Reachability of a `Sym2`-packaged pair of vertices, phrased so it can be
decided at a completely abstract edge (e.g. `G.endpoints a` for an opaque
`a : E`) without ever naming the two vertices involved — see the file
docstring for why that's exactly the property the decision procedure below
needs. -/
def sym2Reachable (H : SimpleGraph V) [DecidableRel H.Adj] : Sym2 V → Prop :=
  Sym2.lift ⟨H.Reachable, fun _ _ => propext SimpleGraph.reachable_comm⟩

/-- `sym2Reachable` is decidable at every, possibly abstract, `Sym2 V`
element. See the file docstring for why `Quot.recOnSubsingleton` applies.
Uses `reachable_iff_mem_bfsClosure`'s efficient `Finset`-BFS characterization
of `Reachable` rather than `infer_instance` (which would silently pull in
Mathlib's exponential `SimpleGraph.instDecidableRelReachable` instead — see
`FastReachable`'s section docstring). -/
instance decSym2Reachable (H : SimpleGraph V) [DecidableRel H.Adj] :
    DecidablePred (sym2Reachable H) := fun z =>
  Quot.recOnSubsingleton (motive := fun z => Decidable (sym2Reachable H z)) z
    (fun p => by
      show Decidable (H.Reachable p.1 p.2)
      exact decidable_of_iff _ (reachable_iff_mem_bfsClosure H p.1 p.2).symm)

end ReachableOnSym2

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

section Decide

variable [Fintype V] [DecidableEq V] [DecidableEq E]

omit [DecidableEq E] in
private theorem coe_setOf_mem_cons (a : E) (l : List E) :
    ({e | e ∈ (a :: l)} : Set E) = insert a {e | e ∈ l} := by
  ext x; simp [List.mem_cons]

omit [DecidableEq E] in
private theorem coe_setOf_mem_cons_of_mem {a : E} {l : List E} (ha : a ∈ l) :
    ({e | e ∈ (a :: l)} : Set E) = {e | e ∈ l} := by
  ext x
  simp only [Set.mem_setOf_eq, List.mem_cons]
  exact ⟨fun h => h.elim (fun h => h ▸ ha) id, Or.inr⟩

/-- **The single-insertion decision, reusable against a fixed base forest.**
Given `{e' | e' ∈ l}` is already known to be a forest, decide whether
`insert a {e' | e' ∈ l}` still is — *one* reachability check against `l`'s
own simple graph. Factored out of `instDecidableIsForestOfList` (which uses
it for its own `a :: rest` case below) specifically so a caller checking
*many* candidate insertions against the *same* already-verified base forest
(a certificate's per-piece maximality check, in `CertChecker.lean`) can call
this directly, paying for one reachability check per candidate instead of
re-deciding the whole `a :: l`-shaped forest from scratch each time — which
would silently repeat `O(|l|)` nested reachability checks, one per
recursion level `instDecidableIsForestOfList` unwinds through. -/
def decidableIsForestInsertOfList (l : List E) (a : E) (hF : G.IsForest ({e | e ∈ l} : Set E)) :
    Decidable (G.IsForest ({e | e ∈ (a :: l)} : Set E)) :=
  if ha : a ∈ l then
    isTrue (by rw [coe_setOf_mem_cons_of_mem ha]; exact hF)
  else if hloop : (G.endpoints a).IsDiag then
    isFalse (fun hFs => (hFs.1 a (by
      rw [coe_setOf_mem_cons]; exact Set.mem_insert a _)) hloop)
  else if hreach : sym2Reachable (G.toSimpleGraph {e | e ∈ l}) (G.endpoints a) then
    isFalse (fun hFs => by
      induction huv : G.endpoints a with
      | _ u v =>
      have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
      have hFs' : G.IsForest (insert a ({e | e ∈ l} : Set E)) := by
        rw [← coe_setOf_mem_cons]; exact hFs
      have hreach' : sym2Reachable (G.toSimpleGraph {e | e ∈ l}) (s(u, v) : Sym2 V) :=
        huv ▸ hreach
      exact (isForest_insert_iff G hF ha huv hne).mp hFs' hreach')
  else
    isTrue (by
      induction huv : G.endpoints a with
      | _ u v =>
      have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
      have hnr : ¬ (G.toSimpleGraph {e | e ∈ l}).Reachable u v := fun hcontra => by
        have hcontra' : sym2Reachable (G.toSimpleGraph {e | e ∈ l}) (s(u, v) : Sym2 V) :=
          hcontra
        exact hreach (huv ▸ hcontra')
      rw [coe_setOf_mem_cons]
      exact (isForest_insert_iff G hF ha huv hne).mpr hnr)

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

section Components

/-!
**A components cache, for callers checking many candidate insertions
against the same base forest.** `decidableIsForestInsertOfList` (`Decide`
above) is already a *single* cheap reachability check — but a certificate's
maximality check calls it once per candidate edge (`CertChecker.lean`'s
`checkTree`, `O(|piece edges|)` candidates against the *same* base forest),
and each call independently reruns `bfsClosure` from scratch, even though
the underlying graph never changes across those calls. `forestComponents`
below computes that graph's connected components *once* — reusing
`bfsClosure`'s already-proven correctness, called only once per distinct
component rather than once per candidate — so repeated queries become
cheap `Finset`/`List` lookups. Confirmed necessary, not just a nicety: on
`nested.certificate.json`'s 190-edge piece, a single reachability query
against an already-built ~19-edge forest measured the same cost whether or
not `instDecidableIsForestOfList`'s own per-level redundancy was fixed
first — the dominant cost was *always* the `O(|piece edges|)`-many
independent fresh queries, not the recursion shape.
-/

variable [Fintype V] [DecidableEq V]

/-- The (at most 2-element) vertex set of a `Sym2 V` edge value, extracted
without ever naming which vertex is "first" — swap-invariance here is the
trivial fact `{u, v} = {v, u}` as `Finset`s, unlike trying to extract an
*ordered* pair (which would need extra structure on `V`; see
`FastReachable`'s docstring for why that route was rejected elsewhere in
this file). -/
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

/-- Every component recorded so far is a *true* `H`-component: the
`bfsClosure` of some seed all of whose own elements are already known to be
mutually `H`-reachable (true, in `forestComponents` below, of a seed formed
from a single edge's own two endpoints). -/
def ValidComponents (H : SimpleGraph V) [DecidableRel H.Adj] (P : List (Finset V)) : Prop :=
  ∀ c ∈ P, ∃ seed : Finset V, c = bfsClosure H seed ∧ ∀ p ∈ seed, ∀ q ∈ seed, H.Reachable p q

theorem ValidComponents.reachable_of_connected {H : SimpleGraph V} [DecidableRel H.Adj]
    {P : List (Finset V)} (hP : ValidComponents H P) {p q : V} (hpq : connected P p q) :
    H.Reachable p q := by
  rcases hpq with rfl | ⟨c, hcP, hpc, hqc⟩
  · exact SimpleGraph.Reachable.refl p
  · obtain ⟨seed, rfl, hseed⟩ := hP c hcP
    obtain ⟨s1, hs1, hs1p⟩ := (mem_bfsClosure_iff H seed p).mp hpc
    obtain ⟨s2, hs2, hs2q⟩ := (mem_bfsClosure_iff H seed q).mp hqc
    exact hs1p.symm.trans ((hseed s1 hs1 s2 hs2).trans hs2q)

/-- Merge `verts` into the partition `P`: skip if some existing component
already covers it (its connectivity information is already accounted for);
otherwise record its whole `bfsClosure` — the genuine, complete `H`-component
containing it, computed once, reused for every later query. -/
def buildComponents (H : SimpleGraph V) [DecidableRel H.Adj] :
    List (Finset V) → List (Finset V) → List (Finset V)
  | [], P => P
  | verts :: rest, P =>
      if _ : ∃ c ∈ P, verts ⊆ c then buildComponents H rest P
      else buildComponents H rest (bfsClosure H verts :: P)

theorem subset_buildComponents (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)) (c : Finset V), c ∈ P →
      c ∈ buildComponents H seeds P
  | [], _, _, hc => hc
  | _ :: rest, P, c, hc => by
      unfold buildComponents
      split
      · exact subset_buildComponents H rest P c hc
      · exact subset_buildComponents H rest _ c (List.mem_cons_of_mem _ hc)

theorem validComponents_buildComponents (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)),
      (∀ verts ∈ seeds, ∀ p ∈ verts, ∀ q ∈ verts, H.Reachable p q) →
      ValidComponents H P → ValidComponents H (buildComponents H seeds P)
  | [], _, _, hP => hP
  | verts :: rest, P, hseeds, hP => by
      unfold buildComponents
      split
      · exact validComponents_buildComponents H rest P
          (fun v hv => hseeds v (List.mem_cons_of_mem _ hv)) hP
      · refine validComponents_buildComponents H rest _
          (fun v hv => hseeds v (List.mem_cons_of_mem _ hv)) ?_
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨verts, rfl, hseeds verts List.mem_cons_self⟩
        · exact hP c hc

theorem covers_buildComponents (H : SimpleGraph V) [DecidableRel H.Adj] :
    ∀ (seeds : List (Finset V)) (P : List (Finset V)) (verts : Finset V), verts ∈ seeds →
      ∃ c ∈ buildComponents H seeds P, verts ⊆ c
  | v :: rest, P, verts, hverts => by
      unfold buildComponents
      split
      · next h =>
        rcases List.mem_cons.mp hverts with rfl | hverts'
        · obtain ⟨c, hcP, hsub⟩ := h
          exact ⟨c, subset_buildComponents H rest P c hcP, hsub⟩
        · exact covers_buildComponents H rest P verts hverts'
      · next h =>
        rcases List.mem_cons.mp hverts with rfl | hverts'
        · exact ⟨bfsClosure H verts, subset_buildComponents H rest _ _ List.mem_cons_self,
            subset_bfsClosure H verts⟩
        · exact covers_buildComponents H rest _ verts hverts'

variable [DecidableEq E]

/-- The connected-components cache of `{e | e ∈ l}`'s own simple graph:
fold over `l`'s edges (as `edgeVerts` seeds), merging into a component
partition as described above. -/
def forestComponents (l : List E) : List (Finset V) :=
  buildComponents (G.toSimpleGraph {e | e ∈ l}) (l.map (fun e => edgeVerts (G.endpoints e))) []

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
theorem validComponents_forestComponents (l : List E) :
    ValidComponents (G.toSimpleGraph {e | e ∈ l}) (forestComponents G l) :=
  validComponents_buildComponents _ _ _
    (fun verts hv => by
      simp only [List.mem_map] at hv
      obtain ⟨e, he, rfl⟩ := hv
      exact mem_edgeVerts_reachable G l he)
    (fun c hc => absurd hc (List.not_mem_nil))

omit [DecidableEq E] in
/-- **Correctness of the components cache.** `p`/`q` lie in a common
component of `forestComponents G l` iff they're reachable in `l`'s own
simple graph. Soundness is `ValidComponents.reachable_of_connected`;
completeness peels the first edge off a `p`–`q` walk (`p ≠ q` forces one to
exist), whose `edgeVerts` seed — being one of `l`'s own edges — is
guaranteed `covers_buildComponents`-covered by some final component, which
(being a true `bfsClosure`-component, `mem_bfsClosure_iff`) already reaches
every vertex `p` itself reaches, `q` included. -/
theorem connected_forestComponents_iff (l : List E) (p q : V) :
    connected (forestComponents G l) p q ↔ (G.toSimpleGraph {e | e ∈ l}).Reachable p q := by
  have hvalid := validComponents_forestComponents G l
  constructor
  · exact hvalid.reachable_of_connected
  · intro hreach
    by_cases hpq : p = q
    · exact Or.inl hpq
    · have hw := hreach
      obtain ⟨w⟩ := hw
      cases w with
      | nil => exact absurd rfl hpq
      | @cons _ x _ hadj rest =>
        obtain ⟨e, he, heq⟩ : ∃ e ∈ l, G.endpoints e = s(p, x) := by
          rw [Multigraph.toSimpleGraph, SimpleGraph.fromEdgeSet_adj] at hadj
          obtain ⟨⟨e, he, heq⟩, -⟩ := hadj
          exact ⟨e, he, heq⟩
        have hpmem : p ∈ edgeVerts (G.endpoints e) := by rw [heq, edgeVerts_mk]; simp
        obtain ⟨c, hcP, hsub⟩ := covers_buildComponents (G.toSimpleGraph {e' | e' ∈ l})
          (l.map (fun e' => edgeVerts (G.endpoints e'))) [] (edgeVerts (G.endpoints e))
          (List.mem_map.mpr ⟨e, he, rfl⟩)
        have hpc : p ∈ c := hsub hpmem
        obtain ⟨seed, hceq, hseedR⟩ := hvalid c hcP
        obtain ⟨s1, hs1, hs1p⟩ := (mem_bfsClosure_iff _ seed p).mp (hceq ▸ hpc)
        have hs1q : (G.toSimpleGraph {e' | e' ∈ l}).Reachable s1 q := hs1p.trans hreach
        have hqc : q ∈ c := hceq ▸ (mem_bfsClosure_of_reachable _ hs1 hs1q)
        exact Or.inr ⟨c, hcP, hpc, hqc⟩

/-- **The fast single-insertion decision, backed by a precomputed
components cache.** Same statement and result as
`decidableIsForestInsertOfList`, but the reachability half is a `List`/
`Finset` lookup against `comps` (assumed to already be `forestComponents G
l`) instead of a fresh `bfsClosure` search — the version to call from a
loop testing many candidate insertions against the same base forest. -/
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

end DiscreteModulusCert
