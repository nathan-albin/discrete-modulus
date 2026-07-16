import DiscreteModulusCert.ForestDecide
import Lean.Data.Json

/-!
# A runnable JSON certificate checker

PR 5's first genuinely standalone verifier: reads a certificate JSON file
(`scratch/certificate_schema.json`, v4) at *program runtime* and checks
every invariant `validate_certificate` (the untrusted Python-side sanity
check) checks, but this time using the same computable decidability
instance `ForestDecide.lean` built (`instDecidableIsForestOfList`) --
genuinely running Cunningham/forest-decision code against the parsed data,
not just a syntactic sanity check.

**Why this is a plain executable, not `decide`/`native_decide` on a proof
term.** `HouseCert.lean` proved facts about *specific, hand-transcribed
edge-index literals* -- data known when Lean itself was compiled, so
`decide`/`native_decide` (tactics that close a proof goal once, at
elaboration time) were the right tool. A certificate's actual content is
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

**What this does and doesn't establish (see `Certification_Plan.md` §5.1.6
follow-up items).** This checks exactly what `validate_certificate` checks,
faithfully and independently, using the real forest-decision algorithm
rather than a syntactic proxy: piece edges disjoint and covering the whole
graph, every declared tree is a genuine forest and maximal within its
piece (so a genuine base of that piece's matroid, via the same
`isBase_contract_restrict_iff_isForest` reduction `HouseCert.lean` uses),
and weights nonnegative and summing to 1 per piece. It does *not* yet
produce a Lean proof TERM (a `Pmf`/`PieceList` value) the kernel has
type-checked -- that needs a separate, universally-quantified soundness
theorem ("if this checker returns `ok`, a genuine `PieceList`/`Pmf` exists
for the same data"), proved once at compile time over arbitrary input,
linking this computable checker to the noncomputable `Pmf` machinery the
way `instDecidableIsForestOfList` already links `decide` to `IsForest`.
Tracked as the next step, not yet done here.
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
instance search (and hence real computation) sees through it. Ported from
`HouseCert.lean`; kept in sync by hand until these two files are merged
into one shared library (tracked as a follow-up). -/
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
halves, computed directly rather than proved about fixed literals). -/
def checkTree (G : Multigraph V E) (I₀acc A T : List E) : Except String PUnit := do
  let _ ← check T.Nodup "tree has a duplicate edge index"
  let _ ← check (T.all (· ∈ A)) "tree uses an edge outside its own piece"
  let _ ← check (decide (G.IsForest (S (I₀acc ++ T))))
    "declared tree together with the prior representative base isn't a forest"
  let extra := A.filter (· ∉ T)
  check (extra.all (fun e => !decide (G.IsForest (S (I₀acc ++ (e :: T))))))
    "declared tree isn't maximal in its piece"

/-- Checks one piece's whole local pmf: every declared tree passes
`checkTree`, weights are nonnegative, and they sum to exactly `1`. Returns
the piece's own edge list `A` and the *first* declared tree (an arbitrary
choice; matroid theory guarantees any one works, see
`HouseCert.lean`'s `piece2_hI₀`) as the new representative to fold into
the next piece's `I₀acc`. -/
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

/-- Checks a whole parsed certificate: builds the graph, folds
`checkPieces` over every piece, and confirms the result is a genuine
partition of the graph's own edges (every edge covered, exactly once --
`Nodup` plus matching length is enough, since every edge in the
accumulated list is already known, by `checkPieces`'s own disjointness
check, to be distinct from every other piece's). -/
def checkCertificate (raw : RawCertificate) : Except String Unit := do
  if raw.certificate_version = 4 then pure ()
  else Except.error s!"unsupported certificate_version {raw.certificate_version}"
  let cg ← buildGraph raw.graph
  let G := cg.toMultigraph
  let m := cg.endpoints.size
  let toE : Nat → Except String (Fin m) := natToFin m
  let Uacc ← checkPieces G toE raw.pieces [] [] 0
  if Uacc.length = m then pure ()
  else Except.error s!"pieces cover {Uacc.length} of {m} edges -- not a partition"

def checkCertificateJson (s : String) : Except String Unit := do
  let j ← Json.parse s
  let raw ← fromJson? (α := RawCertificate) j
  checkCertificate raw

end CertChecker
end DiscreteModulusCert
