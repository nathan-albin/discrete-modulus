# The pipeline, in detail

This walks through each of the three stages from [`README.md`](README.md),
naming the actual files and functions responsible. Read
[`walkthrough.md`](walkthrough.md) first if you haven't — it shows what
each stage produces on a concrete example; this explains how.

## 1. Solver instrumentation

**Files:** `cpp/include/discrete_modulus/cunningham.hpp`,
`cpp/include/discrete_modulus/solver_trace.hpp`.

`spanning_tree_modulus` (`cunningham.hpp`) computes spanning tree modulus
by repeatedly extracting a *tight set*: a subset of edges `crit_set`
whose induced density exactly equals the current subproblem's modulus
`theta`, dispatching those edges at $\eta^* = \theta$ and recursing on
whatever components remain once `crit_set` is removed. This is the
solver's entire strategy — modulus reduces to finding these tight sets
one at a time (Cunningham's matroid-greedy algorithm for polymatroid
bases, adapted to the graphic matroid; see the companion book's "Exact
Spanning Tree Modulus" chapter for the underlying theory).

The certificate builder needs to replay this decomposition without
re-running the solver, so `spanning_tree_modulus` takes an optional
`SolverTrace* trace` parameter (default `nullptr`, no behavior change for
existing callers). When non-null, it appends one `TraceRound` per
round — the component's vertex set, the `crit_set` dispatched, and
`theta` — and `write_trace_json` serializes the whole `SolverTrace` as
`<prefix>.trace.json` (schema: see [`schema.md`](schema.md)). Vertex ids
in the trace are the *original* graph's vertex descriptors, not a
round-local renumbering, so the trace is self-contained and the builder
never needs to replay the solver's own internal component graphs.

`spanning_tree_modulus` assumes its input is a simple graph (`graphs.hpp`'s
`is_simple_graph`) — the solver itself is never handed a multigraph,
even though the shrunk multigraphs the certificate builder constructs
*conceptually* (step 2 below) are a separate, purely downstream
construction the solver has no knowledge of.

## 2. Certificate builder

**Files:** `python/src/discrete_modulus/certificate_builder.py`,
`core_deflation.py`, `pmf_construction.py`, `tree_packing.py`.

Per round of the trace, `certificate_builder.py`:

1. **Reconstructs the round's own working graph** exactly, as
   `g.subgraph(round.vertices)` — valid because a `crit_set` edge always
   connects two components later rounds resolve, so no earlier round's
   dispatched edges can spuriously reappear.
2. **Shrinks it**: the round's own pieces (connected components after
   removing `crit_set`) collapse to points, with `crit_set` kept as edges
   between them — genuinely a multigraph in general (two different pairs
   of pieces can be joined by more than one `crit_set` edge).

   Steps 1–2 were confirmed computationally against `examples/nested`'s
   real 3-round trace before this module was written: round 0's 60 raw
   vertices contract to 21 pieces, round 1's 40 contract to 21, and
   round 2 (20 vertices) needs no contraction at all — and round 1's
   shrunk multigraph does have genuine parallel edges (multiplicity up to
   3), confirming a `MultiGraph`-aware pmf construction really is
   necessary in general, not just a defensive abstraction.
3. **Builds a pmf on this shrunk multigraph's spanning trees**
   (`pmf_construction.build_factored_pmf`, next section) — a distribution
   whose marginal is uniformly the round's own recorded `theta`, asserted
   as a build-time sanity check.
4. **Translates local edge indices to global ones** and appends the
   result to the certificate's flat `pieces` list, **in reverse round
   order**: a certificate's laminar-family fold needs "dependencies
   before dependents" order, but the solver dispatches outermost-first
   (round 0's tight set runs *between* the components round 1, round 2,
   ... go on to resolve, so round 0 depends on them, not the reverse).
   Reversing dispatch order — a pre-order traversal — always produces a
   valid dependency order, for any branching shape, not just the linear
   chains `house`/`nested`'s examples happen to be. Within one round,
   core-before-rigid-base order (step 3's own discovery order) is
   already correct and untouched.

### Building the pmf for one (multi)graph: deflation + tree packing

Every shrunk multigraph the solver dispatches is *homogeneous*: no
vertex-induced subgraph has strictly larger spanning-tree density
$|E(H)|/(|V(H)|-1)$ than the whole graph's own. Homogeneous splits into
two cases:

- **Strictly homogeneous** (every proper subgraph is strictly less
  dense): a uniform pmf on spanning trees exists directly, no "forbidden
  trees."
- **Merely homogeneous**: some proper subgraph — a "core" — ties the
  whole graph's own density, meaning a uniform marginal would need some
  spanning trees to carry negative weight.

`core_deflation.py`'s `find_core` locates the minimal tied subgraph (via
an exact-integer max-flow construction — no floating-point tolerance
issues, unlike the continuous log-weight formulation this was adapted
from), and `pmf_construction.build_factored_pmf` repeatedly finds and
peels off the top core until only a strictly homogeneous rigid base
remains — each core, once contracted away, provably exposes a new,
smaller core one level down, so this always terminates at a rigid base
with no forbidden trees at all (Albin, Lind, Melikyan, Poggi-Corradini,
"Minimizing the Determinant of the Graph Laplacian," *Journal of Graph
Theory*, 2025, Theorem 8.1).

Each resulting piece (a core, or the final rigid base) is strictly
homogeneous with a single uniform target `theta = p/q` in lowest terms —
so its exact uniform pmf is known in closed form: build `q` spanning
trees such that every edge is used in exactly `p` of them, weight each
`1/q`. `tree_packing.build_tree_packing` constructs this directly, by a
two-tier local search (an away-step tree-for-tree swap that provably
never increases the coverage-imbalance energy, falling back to a BFS
matroid-exchange search when the swap alone stalls) — no continuous
optimization at all, and no risk of the unpredictable convergence tail an
earlier Frank-Wolfe-based approach
(`python/src/discrete_modulus/min_norm_point.py`) had on some pieces from
pure vertex/edge-labeling sensitivity. `min_norm_point.py` is kept for
its own comparison value (and a planned book chapter on the underlying
Frank-Wolfe theory) but is no longer on the production path.

The result, `pmf_construction.FactoredPmf`, represents the whole
distribution *factored*: one independent local pmf per piece, plus each
piece's edge provenance back to the original graph, rather than
materializing a flat list over the whole graph's spanning trees (which
would blow up combinatorially in the number of pieces). Picking a genuine
spanning tree is "independently sample one local tree per piece, union
the results" — correct because the pieces partition the graph's edges.
This factored shape is exactly what the certificate's `pieces` array
records, and exactly what the Lean side's `PieceList`/`Pmf.glue` machinery
(below) is built to consume without ever materializing the combinatorial
product either.

### `eta`/`rho`, and the builder's own sanity checks

`compute_eta_from_pieces` sums each declared tree's weight into every
edge it touches — the same per-piece composition the Lean side proves
sound (`Pmf.glue_marginal`/`PieceList.glueAll_marginal`, linear in
pieces × edges, never the exponential combinatorial product).
`compute_rho` is then just $\rho = \eta / \|\eta\|^2$.
`validate_certificate` re-derives both from `pieces` and asserts they
match the certificate's own declared fields before the builder writes the
file — catching builder bugs cheaply, long before a Lean run, though it
is not a substitute for the Lean proof (nothing in the Python package is
trusted).

## 3. The Lean verifier

**Directory:** `lean/DiscreteModulusCert/`. Depends on
[`lean-modulus`](https://github.com/nathan-albin/lean-modulus) (pinned to
a specific commit) for its graph/matroid infrastructure
(`Multigraph`, `graphicMatroid`).

### The math: Cauchy-Schwarz duality (`Optimality.lean`)

For an admissible density $\rho$ (every spanning tree has $\rho$-weight
$\ge 1$) and any pmf $\mu$ on spanning trees with marginal
$\eta = \mathcal{N}^T\mu$, Cauchy-Schwarz gives
$1 \le \langle \rho, \eta \rangle \le \|\rho\| \|\eta\|$. If equality
holds — which happens exactly when $\rho = \eta / \|\eta\|^2$ — then
$\rho$ and $\mu$ are *simultaneously* optimal: $\rho$ minimizes
$\|\rho\|^2$ over every admissible density (solving the modulus problem),
and $\eta$ minimizes $\|\eta\|^2$ over the marginals of every pmf
(solving the dual min-norm-point problem — the quantity
`tree_packing`/`min_norm_point` compute). `certificate_optimality`
(`Optimality.lean`) is this argument, proved once, generically, over a
small self-contained `ℚ`-valued vocabulary (`Family.lean`'s `CertDensity`,
`sqNorm`, `Pmf`) rather than `lean-modulus`'s own `ℝ≥0`-valued
`Density`/`Adm` — Mathlib's finite Cauchy-Schwarz needs a genuine ordered
ring, which `ℝ≥0` (no subtraction) isn't.

### Gluing pieces into one pmf (`Glue.lean`)

A certificate's `pieces` array is a flat, ordered list of blocks, each
typed relative to everything listed before it (already "contracted
away"). `Glue.lean` proves this is enough to reconstruct a genuine pmf on
the *whole* graph's spanning trees:
`isBase_union_of_isBase_restrict_isBase_contract` (a general matroid fact:
a base of a restriction to a block, plus a base of the contraction by
that block, unions to a base of the whole matroid) lifts to `Pmf.glue`
(gluing two pmfs), which folds down a whole `PieceList` via `glueAll`.
Critically, `Pmf.glue_marginal`/`PieceList.glueAll_marginal` prove the
glued pmf's marginal is exactly the *sum* of every piece's own local
marginal — computable in time linear in pieces × edges, never touching
`Pmf.glue`'s own combined support (a literal Cartesian product,
exponential in piece count). This is what lets the verifier check a
certificate's `eta`/`rho` fields at all.

### Reducing "is this a genuine base" to "is this a forest" (`IsBaseCheck.lean`, `ForestDecide.lean`)

A certificate declares each tree as a plain edge-index list; checking it's
really a base of its piece's matroid is reduced
(`isBase_contract_restrict_iff_isForest`) to two checks against the
*original* graph directly, no contraction/relabeling needed: (a) is
`I₀ ∪ T` a forest (given `I₀`, an already-verified representative tree of
everything processed so far), and (b) is it maximal (no other edge of the
piece can be added without creating a cycle) — a finite, single-insertion
check, sufficient by the matroid exchange property.
`Multigraph.IsForest` itself needed a genuine, computable `Decidable`
instance to make this checkable at runtime at all (`ForestDecide.lean`,
structural recursion on the candidate edge list) — Mathlib's own natural
route through `Reachable`/`IsBridge` decidability doesn't synthesize.

### The runnable checker (`CertChecker.lean`, `Kruskal.lean`, `Admissibility.lean`)

`CertChecker.checkCertificate` is the executable entry point: parses a
certificate JSON (`Lean.Data.Json` + `deriving FromJson`), folds
`checkPiece`/`checkPieces` over `pieces` (each piece's forest/maximality/
weight checks above), confirms the pieces partition the graph's edges,
recomputes `eta`/`rho` and rejects on mismatch, and finally runs
`Kruskal.run` (a plain greedy union-find MST implementation) against the
recomputed `rho`, rejecting if the minimum spanning tree's weight is
`< 1`. This is a plain executable, not a `decide`/`native_decide` proof
term — a certificate's content is only known at *runtime* (read from a
file path), so there's no fixed goal for an elaboration-time tactic to
close. `lean/Main.lean`'s `verify_cert` is the compiled CLI wrapping it.

`Admissibility.lean`'s `Kruskal.run_isAdmissible_of_weight_ge_one` is the
one place trust enters: it bridges "Kruskal's computed weight is `≥ 1`"
directly to `IsAdmissible`, as a named `axiom` rather than a proof — see
[`trust.md`](trust.md).

### From "checker accepts" to a kernel-checked proof (`Soundness.lean`)

Running `checkCertificate` and getting `ok` back is, by itself, a runtime
fact — not yet a term the kernel has type-checked. `Soundness.lean`
closes that gap generically, for *any* certificate the checker accepts,
not a hand-picked example: `checkCertificate_sound` shows acceptance
implies a genuine `Pmf`/`PieceList` exists (built from `checkPieces_sound`,
threading the forest/maximality proofs above through the fold) with the
declared `rho` admissible and the declared `eta` exactly equal to the
constructed pmf's marginal; `checkCertificate_optimal` wires this directly
into `certificate_optimality`, concluding both halves of "simultaneously
optimal" for the accepted certificate.

### A concrete instance (`EndToEndTest.lean`)

`EndToEndTest.lean`'s `house_end_to_end_optimal`/`nested_end_to_end_optimal`
prove the full conclusion — a real, on-disk certificate file's density and
pmf really are simultaneously optimal — for the actual bytes the Python
builder produced, parsed by the real JSON parser at compile time
(`include_str`) and checked via `native_decide`, not hand-transcribed.
(An earlier version of this file, `HouseCert.lean`, validated the whole
per-piece-verification-then-gluing pipeline by hand-transcribing the
house certificate's data into Lean literals, before a JSON parser or the
generic `Soundness.lean` theorems existed; removed once `EndToEndTest.lean`
made it redundant. Its one genuinely distinct result — that house's
uniform `rho` needs no Kruskal axiom at all — lives on as
`Admissibility.lean`'s `isAdmissible_const_div_ncard_of_isBase`.)

### A couple of implementation notes

- **`native_decide` vs. `decide`.** Several checks (`Multigraph.IsForest`
  on real certificate data, the parsed-JSON end-to-end tests) use
  `native_decide` rather than `decide`: some of Mathlib's own decidability
  instances are built in a way the kernel's own reduction can't unfold, or
  are simply too slow for the kernel to evaluate on realistically-sized
  pieces. `native_decide` compiles to native code instead, at the standard
  cost of an extra trusted-compiler axiom per callsite (see
  [`trust.md`](trust.md)).
- **No generic computable `E → Fin m` projection.** `CertChecker.lean`'s
  `sumTreeContributions` works directly over `Nat`-indexed raw JSON data
  rather than through the file's own generic `{V E} [Fintype E]`
  abstraction, because `Fintype.equivFin` is `noncomputable` — there is no
  way to turn an abstract `Fintype E` into a concrete `Fin m` index
  generically at runtime. This same obstacle shows up more than once in
  this codebase; CERTDOC tags at each occurrence should eventually link
  here with the specifics.
