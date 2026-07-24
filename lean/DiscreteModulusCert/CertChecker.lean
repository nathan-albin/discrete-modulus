import DiscreteModulusCert.ForestDecide
import DiscreteModulusCert.Kruskal
import Lean.Data.Json

/-!
# A runnable JSON certificate checker

A genuinely standalone verifier: reads a certificate JSON file at
*program runtime* and checks every invariant `validate_certificate` (the
untrusted Python-side sanity check) also checks, but this time using the
same computable decidability instance `ForestDecide.lean` built
(`instDecidableIsForestOfList`) -- genuinely running Cunningham/forest-
decision code against the parsed data, not just a syntactic sanity check.
A certificate is a JSON object with a top-level graph (vertex count plus
a global edge list), a flat ordered `pieces` array (each piece its own
edge subset plus a local pmf over that piece's own spanning trees, as
edge-index lists with rational weights), and top-level `eta`/`rho` arrays
(one rational per edge) -- see `RawCertificate`/`RawPiece`/`RawTree`
below for the exact shape parsed.

See `docs/certification/schema.md` for the authoritative field-by-field
certificate schema reference, and
`docs/certification/certificate_schema.json` for the machine-checkable
JSON Schema.

**Checked (not trusted) `eta`/`rho` fields.** The certificate declares
the optimal pmf's marginal (`eta`) and admissible density (`rho`)
per edge; this checker recomputes both independently from `pieces` (the
same composition `Pmf.glue_marginal`/`PieceList.glueAll_marginal`,
`Glue.lean`, prove sound -- linear in pieces x edges, never the glued
pmf's exponential support) and rejects the certificate if the declared
values don't match. Nothing is trusted that wasn't already being derived;
the certificate's own `eta`/`rho` are just now legible without running
this checker at all, and diffable directly against the C++ solver's own
`*.eta` output.

**Admissibility of `rho`, via the accepted Kruskal-oracle gap
(`Kruskal.lean`).** `rho` is admissible iff *every* spanning tree has
`rho`-weight `≥ 1`, which holds iff the *minimum*-weight spanning tree
does. `Kruskal.run` computes that minimum greedily; its correctness (that
the greedy algorithm's output really is a minimum spanning tree) is this
project's one deliberately unverified step -- the result is trusted, not
proven. This checker still genuinely rejects a certificate whose
Kruskal-computed minimum weight is `< 1`; only the *algorithm's own
correctness*, not whether the check runs, is unverified.

**Why this is a plain executable, not `decide`/`native_decide` on a proof
term.** `EndToEndTest.lean` proves facts about *specific* certificates
whose data is fixed at elaboration time (embedded via `include_str`), so
`decide`/`native_decide` (tactics that close a proof goal once, at
elaboration time) are the right tool there. A certificate's actual content is
only known when this program *runs* (read from a file path given on the
command line), so there is no fixed goal for a tactic to close at
elaboration time at all. The right tool instead is ordinary functional
code: `instDecidableIsForestOfList` is a genuinely computable `Decidable`
instance (structural recursion, no `Classical.choice` anywhere -- see its
own file), so writing `if G.IsForest (S l) then ... else ...` in a regular
(non-tactic) definition compiles to real executable code that runs the
same forest-decision algorithm against whatever list `l` this program
parsed at runtime. This file's checks are all phrased this way: plain,
computable predicates over `List`/`Fin m`/`ℚ`, never touching `Set E`'s
classical equality (unlike `Pmf.support : Finset (Set E)`, which is
genuinely noncomputable) -- deliberately so, since a runtime checker has to
actually *run*.

**What this does and doesn't establish, by itself.** This checks exactly
what `validate_certificate` checks, faithfully and independently, using
the real forest-decision algorithm rather than a syntactic proxy: piece
edges disjoint and covering the whole graph, every declared tree is a
genuine forest and maximal within its piece (so a genuine base of that
piece's matroid, via the same `isBase_contract_restrict_iff_isForest`
reduction `Soundness.lean`'s `checkTree_sound` uses), and weights
nonnegative and summing to 1 per piece. Running `checkCertificate` and
getting `ok` back is, by itself, only a runtime fact, not a kernel-checked
proof term -- that gap
(a universally-quantified soundness theorem: "if this checker returns
`ok`, a genuine `PieceList`/`Pmf` exists for the same data, and it's
optimal") is closed separately, by `Soundness.lean`'s
`checkCertificate_sound`/`checkCertificate_optimal`, linking this
computable checker to the noncomputable `Pmf`/`certificate_optimality`
machinery the way `instDecidableIsForestOfList` already links `decide` to
`IsForest`.
-/

namespace DiscreteModulusCert
namespace CertChecker

open Lean Multigraph

/-- `[numerator, denominator]`, exactly as the schema requires -- arbitrary
precision (`Int`/`Nat` are unbounded in Lean), never floating point. -/
structure RawTree where
  edges : List Nat
  weight : Int × Nat
deriving FromJson

structure RawLocalPmf where
  trees : List RawTree
deriving FromJson

structure RawPiece where
  edges : List Nat
  local_pmf : RawLocalPmf
deriving FromJson

structure RawGraph where
  num_vertices : Nat
  edges : List (Nat × Nat)
deriving FromJson

structure RawCertificate where
  certificate_version : Nat
  graph : RawGraph
  pieces : List RawPiece
  eta : List (Int × Nat)
  rho : List (Int × Nat)
deriving FromJson

/-- A certificate's graph, with vertex/edge bounds already checked: `E` is
literally `Fin endpoints.size`, so there is no separate "m" field that
could ever drift out of sync with `endpoints`'s actual length. -/
structure CheckedGraph where
  n : Nat
  endpoints : Array (Fin n × Fin n)

def CheckedGraph.toMultigraph (cg : CheckedGraph) :
    Multigraph (Fin cg.n) (Fin cg.endpoints.size) :=
  ⟨fun e => s(cg.endpoints[e].1, cg.endpoints[e].2)⟩

def natToFin (bound n : Nat) : Except String (Fin bound) :=
  if h : n < bound then Except.ok ⟨n, h⟩
  else Except.error s!"index {n} out of range (bound={bound})"

def buildGraph (raw : RawGraph) : Except String CheckedGraph := do
  let n := raw.num_vertices
  let endpoints ← raw.edges.toArray.mapM fun (u, v) => do
    let u' ← natToFin n u
    let v' ← natToFin n v
    return (u', v')
  return ⟨n, endpoints⟩

variable {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

/-- The edge set of an edge-index list, in exactly the `{e | e ∈ l}` shape
`instDecidableIsForestOfList` is stated for -- `abbrev`, not `def`, so
instance search (and hence real computation) sees through it. The single
canonical definition; `Soundness.lean`'s own `S`-manipulation lemmas
import and reuse this one rather than redefining it. -/
abbrev S (l : List E) : Set E := {e | e ∈ l}

/-- Turns a `Bool` check plus an error message into an `Except` action --
gives every check below a single, unambiguous monadic type, rather than
leaving `if cond then pure () else Except.error msg` to be elaborated
polymorphically as a bare `do`-block statement. Returns `PUnit`, not
`Unit`: in a `do` block whose overall result type mentions a
universe-polymorphic `E : Type*` (every caller here), binding a discarded
`Except String Unit` statement hits a universe-unification quirk in the
elaborator (confirmed by direct experiment) that `PUnit` -- already
universe-polymorphic itself -- doesn't. -/
def check (cond : Bool) (msg : String) : Except String PUnit :=
  if cond then Except.ok ⟨⟩ else Except.error msg

/-- Checks one declared tree (`T`, a piece's own edge sublist) against an
already-accumulated representative base `I₀acc` of everything processed so
far: `T ⊆ A`, `I₀acc ++ T` is a forest, and no edge of `A \ T` can be added
without creating a cycle (`isBase_contract_restrict_iff_isForest`'s two
halves, computed directly rather than proved about fixed literals).

The maximality half uses `decidableIsForestInsertOfComponents` against a
components cache built *once* per tree (`forestComponents`) rather than a
fresh `decide (G.IsForest (S (I₀acc ++ (e :: T))))` per candidate `e`. Two
compounding redundancies made the naive version too slow on real
certificate pieces (`nested.certificate.json`'s 190-edge/10-tree piece):
`instDecidableIsForestOfList` recomputes one reachability check per
recursion level (`O(|I₀acc ++ T|)` of them) for *every* candidate, and even
after that was collapsed to a single check per candidate
(`decidableIsForestInsertOfList`), each of those still reran its own
connected-components search against a base graph that never changes across
the whole `A \ T` loop. Building the base graph's connected components once
(see `ForestDecide.lean`'s `mergeStep`/`buildComponents`) and reusing them
for every candidate turns each check into a cheap `List`/`Finset` lookup
instead. -/
def checkTree (G : Multigraph V E) (I₀acc A T : List E) : Except String PUnit := do
  let _ ← check T.Nodup "tree has a duplicate edge index"
  let _ ← check (T.all (· ∈ A)) "tree uses an edge outside its own piece"
  match hd : decide (G.IsForest (S (I₀acc ++ T))) with
  | false => Except.error "declared tree together with the prior representative base isn't a forest"
  | true =>
    have hTforest : G.IsForest (S (I₀acc ++ T)) := of_decide_eq_true hd
    let extra := A.filter (· ∉ T)
    let comps := forestComponents G (I₀acc ++ T)
    check (extra.all (fun e => !(@Decidable.decide _
      (decidableIsForestInsertOfComponents G (I₀acc ++ T) e hTforest comps rfl))))
      "declared tree isn't maximal in its piece"

/-- Checks one piece's whole local pmf: every declared tree passes
`checkTree`, weights are nonnegative, and they sum to exactly `1`. Returns
the piece's own edge list `A` and the *first* declared tree (an arbitrary
choice; matroid theory guarantees any one works, via
`Glue.lean`'s `isBase_contract_iff_of_isBasis_restrict`) as the new
representative to fold into the next piece's `I₀acc`. -/
def checkPiece (G : Multigraph V E) (Uacc : List E) (I₀acc : List E) (raw : RawPiece)
    (toE : Nat → Except String E) : Except String (List E × List E) := do
  let A ← raw.edges.mapM toE
  let _ ← check A.Nodup "piece has a duplicate edge index"
  let _ ← check (A.all (· ∉ Uacc)) "piece's edges overlap an earlier piece"
  let trees ← raw.local_pmf.trees.mapM fun t => do
    let edges ← t.edges.mapM toE
    let _ ← check (!decide (t.weight.2 = 0)) "weight has a zero denominator"
    let w : ℚ := (t.weight.1 : ℚ) / (t.weight.2 : ℚ)
    let _ ← checkTree G I₀acc A edges
    pure (edges, w)
  let T₀ ← match trees.head? with
    | none => Except.error "piece has no trees in its local pmf"
    | some (T₀, _) => Except.ok T₀
  let _ ← check (trees.all (fun t => decide (0 ≤ t.2))) "a tree has a negative weight"
  let _ ← check (decide ((trees.map Prod.snd).sum = 1)) "piece's tree weights don't sum to 1"
  return (A, I₀acc ++ T₀)

/-- Folds `checkPiece` over every piece in order, threading the
accumulated edge list and representative base. Returns the final
accumulated edge list (for the caller to check partition-completeness
against the graph's own edge count). -/
def checkPieces (G : Multigraph V E) (toE : Nat → Except String E) :
    List RawPiece → List E → List E → Nat → Except String (List E)
  | [], Uacc, _, _ => pure Uacc
  | raw :: rest, Uacc, I₀acc, i =>
    match checkPiece G Uacc I₀acc raw toE with
    | .error e => Except.error s!"piece {i}: {e}"
    | .ok (A, I₀acc') => checkPieces G toE rest (Uacc ++ A) I₀acc' (i + 1)

/-- Recomputes the optimal pmf's marginal at every edge (global index),
directly from a certificate's own raw `pieces` -- summing each declared
tree's weight into every edge it uses. Mirrors `compute_eta_from_pieces`
on the Python side (`certificate_builder.py`), but works entirely over
`Nat`/`Fin m` rather than through `checkPiece`/`checkPieces`'s generic
`{V E : Type*} [Fintype E]` abstraction: that abstraction has no
computable `E → Fin m` projection available generically (`Fintype.equivFin`
is `noncomputable`). Working directly from the raw `Nat`-indexed JSON
data, where `m` is already concrete, sidesteps this entirely. See
`docs/certification/pipeline.md`'s "implementation notes" for this same
obstacle in context. -/
def sumTreeContributions (m : Nat) (toE : Nat → Except String (Fin m))
    (pieces : List RawPiece) : Except String (Array ℚ) :=
  pieces.foldlM
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
    (Array.replicate m (0 : ℚ))

/-- Parses a certificate's declared `eta`/`rho` field (a `List (Int ×
Nat)`, one `[numerator, denominator]` pair per edge) into an `Array ℚ`,
checking its length matches the graph's edge count and every denominator
is nonzero. -/
def parseRationalArray (m : Nat) (raw : List (Int × Nat)) (label : String) :
    Except String (Array ℚ) := do
  let _ ← check (decide (raw.length = m)) s!"{label} has {raw.length} entries, expected {m}"
  raw.toArray.mapM fun (num, den) => do
    let _ ← check (!decide (den = 0)) s!"{label} has a zero denominator"
    pure ((num : ℚ) / (den : ℚ))

/-- Checks two same-length `ℚ` arrays are equal, reporting the first
mismatching index (and both values) if not -- used for both the `eta` and
`rho` checks below. -/
def checkQArrayEq (label : String) (computed declared : Array ℚ) : Except String PUnit := do
  let _ ← check (decide (computed.size = declared.size))
    s!"{label}: computed {computed.size} values but certificate declares {declared.size}"
  match (List.range computed.size).find? (fun i => !decide (computed.getD i 0 = declared.getD i 0)) with
  | some i =>
    Except.error s!"{label} mismatch at edge {i}: computed {computed.getD i 0}, declared {declared.getD i 0}"
  | none => pure ()

/-- Checks a whole parsed certificate: builds the graph, folds
`checkPieces` over every piece, confirms the result is a genuine
partition of the graph's own edges (every edge covered, exactly once --
`Nodup` plus matching length is enough, since every edge in the
accumulated list is already known, by `checkPieces`'s own disjointness
check, to be distinct from every other piece's), and finally recomputes
`eta`/`rho` from `pieces` and checks them against the certificate's own
declared fields (checked, not trusted -- see the module docstring). -/
def checkCertificate (raw : RawCertificate) : Except String Unit := do
  if raw.certificate_version = 5 then pure ()
  else Except.error s!"unsupported certificate_version {raw.certificate_version}"
  let cg ← buildGraph raw.graph
  let G := cg.toMultigraph
  let m := cg.endpoints.size
  let toE : Nat → Except String (Fin m) := natToFin m
  let Uacc ← checkPieces G toE raw.pieces [] [] 0
  if Uacc.length = m then pure ()
  else Except.error s!"pieces cover {Uacc.length} of {m} edges -- not a partition"
  let computedEta ← sumTreeContributions m toE raw.pieces
  let declaredEta ← parseRationalArray m raw.eta "eta"
  let _ ← checkQArrayEq "eta" computedEta declaredEta
  let normSq : ℚ := (List.range m).foldl (fun acc i => acc + computedEta.getD i 0 * computedEta.getD i 0) 0
  let _ ← check (!decide (normSq = 0)) "sum of squared etas is zero; rho is undefined"
  let computedRho := computedEta.map (· / normSq)
  let declaredRho ← parseRationalArray m raw.rho "rho"
  let _ ← checkQArrayEq "rho" computedRho declaredRho
  let mstEdges := Kruskal.run cg.n raw.graph.edges.toArray computedRho
  let mstWeight : ℚ := mstEdges.foldl (fun acc i => acc + computedRho.getD i 0) 0
  let _ ← check (!decide (mstWeight < 1))
    s!"admissibility check failed: Kruskal's minimum spanning tree has rho-weight {mstWeight} < 1 \
(UNVERIFIED: relies on an unproven Kruskal implementation -- its output is trusted, not proven, \
to be a genuine minimum-weight spanning tree)"

def checkCertificateJson (s : String) : Except String Unit := do
  let j ← Json.parse s
  let raw ← fromJson? (α := RawCertificate) j
  checkCertificate raw

end CertChecker
end DiscreteModulusCert
