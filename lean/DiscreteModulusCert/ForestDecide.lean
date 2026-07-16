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

This file sidesteps `IsBridge` entirely and builds the decision procedure the
plan anticipated: a verified union-find-style algorithm, phrased as
structural recursion on a `List E` of candidate edges (a certificate's tree
is exactly such a list — an edge-index list, per §6 of the plan), inserting
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
element. See the file docstring for why `Quot.recOnSubsingleton` applies. -/
instance decSym2Reachable (H : SimpleGraph V) [DecidableRel H.Adj] :
    DecidablePred (sym2Reachable H) := fun z =>
  Quot.recOnSubsingleton (motive := fun z => Decidable (sym2Reachable H z)) z
    (fun p => by show Decidable (H.Reachable p.1 p.2); infer_instance)

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

/-- **The decision procedure itself.** Structural recursion on `l : List E`:
`[]` is trivially a forest; for `a :: rest`, decide `G.IsForest {e | e ∈ rest}`
recursively, and if that holds:
- if `a` already occurs in `rest`, the edge set is unchanged — reuse the
  recursive result directly;
- otherwise decide the new edge's insertion via `isForest_insert_iff`,
  checking "`a` is a loop" and "`a`'s endpoints are already connected in
  `rest`" via `Sym2.IsDiag`/`sym2Reachable` (never naming the endpoints, so
  the whole definition stays `decide`-reducible — see the file docstring). -/
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
      | isTrue hF =>
          if ha : a ∈ rest then
            isTrue (by rw [coe_setOf_mem_cons_of_mem ha]; exact hF)
          else if hloop : (G.endpoints a).IsDiag then
            isFalse (fun hFs => (hFs.1 a (by
              rw [coe_setOf_mem_cons]; exact Set.mem_insert a _)) hloop)
          else if hreach : sym2Reachable (G.toSimpleGraph {e | e ∈ rest}) (G.endpoints a) then
            isFalse (fun hFs => by
              obtain ⟨u, v, huv⟩ := Sym2.exists.mp ⟨G.endpoints a, rfl⟩
              have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
              have hFs' : G.IsForest (insert a ({e | e ∈ rest} : Set E)) := by
                rw [← coe_setOf_mem_cons]; exact hFs
              have hreach' : sym2Reachable (G.toSimpleGraph {e | e ∈ rest}) (s(u, v) : Sym2 V) :=
                huv ▸ hreach
              exact (isForest_insert_iff G hF ha huv hne).mp hFs' hreach')
          else
            isTrue (by
              obtain ⟨u, v, huv⟩ := Sym2.exists.mp ⟨G.endpoints a, rfl⟩
              have hne : u ≠ v := fun h => hloop (by rw [huv, h]; exact Sym2.diag_isDiag v)
              have hnr : ¬ (G.toSimpleGraph {e | e ∈ rest}).Reachable u v := fun hcontra => by
                have hcontra' : sym2Reachable (G.toSimpleGraph {e | e ∈ rest}) (s(u, v) : Sym2 V) :=
                  hcontra
                exact hreach (huv ▸ hcontra')
              rw [coe_setOf_mem_cons]
              exact (isForest_insert_iff G hF ha huv hne).mpr hnr)

end Decide

end DiscreteModulusCert
