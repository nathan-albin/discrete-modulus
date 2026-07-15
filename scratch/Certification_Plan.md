# Plan: formally certifying the C++ exact-arithmetic spanning tree modulus solver

Source material: [`Certification_Thoughts.md`](Certification_Thoughts.md). This
document turns those notes into a staged, checklist-driven plan. Decisions
locked in during planning (so we don't re-litigate them mid-implementation):

> **Read this note before the rest of the doc if you're picking this up
> fresh.** The "medium gap" story below (Wolfe's algorithm alone) turned out
> to be *necessary but not sufficient* once tested against real multi-round
> data — see the "Medium gap, revised" bullet immediately below and the new
> §5.1.5 for the actual current architecture (deflation + Wolfe's algorithm
> per piece). The rest of the document (Phase 0, PR 2's original checklist,
> §5.1's Wolfe-vs-column-generation writeup) is kept as-is for the history —
> don't delete it — but treat §5.1.5 and the "Medium gap, revised" bullet as
> overriding wherever they conflict with older text.

- **Start here (but it's not a single blocking gate):** Phase 0 (§4) —
  implementing the pmf-construction algorithm as its own standalone piece of
  the `python/` package, with a book chapter. Not part of the original plan;
  added because it's needed for PR 2 regardless, and doing it first gives a
  place to learn/tune/test it in isolation before it's load-bearing. But
  only `min_norm_point.py` blocks PR 2 specifically — Phase A and Phase B
  don't depend on Phase 0 at all, and the book chapter blocks nothing ever
  (see Phase 0's dependency note in §4) — so Phase A/B and Phase 0 can all
  run in parallel rather than strictly in sequence. **Status: `min_norm_point.py`
  is done and merged (`python/src/discrete_modulus/min_norm_point.py`); the
  book chapter has not been started.**
- **Lean toolchain:** Lean 4 + Mathlib. **Confirmed working**: a throwaway
  spike (§4 Phase B) pulled `lean-modulus` in as a pinned Lake dependency
  and built cleanly against Mathlib — see §4's Phase B update.
- **Medium gap** (sparse per-round pmf construction): **originally confirmed
  as Wolfe's minimum-norm-point algorithm alone (§5.1); revised after real
  multi-round validation surfaced a real failure mode Wolfe's algorithm
  cannot resolve on its own — see §5.1.5, the current source of truth.**
  Summary: Wolfe's algorithm (§5.1) is exactly right for a *strictly
  homogeneous* shrunk graph (no proper subgraph ties the graph's own
  density), converging fast with an explicit eviction mechanism for bad
  trees. But real solver-dispatched shrunk multigraphs are only guaranteed
  *homogeneous*, not *strictly* homogeneous — some have a proper "core"
  subgraph tied at the same density (the graph's own theory calls these
  "forbidden trees": some spanning trees can never appear in any
  feasible uniform-marginal pmf). Wolfe's algorithm run directly on such a
  graph doesn't fail cleanly — it grows its active set without bound
  chasing a target it can't exactly reach, confirmed on the real round-2
  piece of `examples/nested` (K20-shaped, `|C|=190`). §5.1.5 covers the
  fix: **deflate first** (`core_deflation.py`, exact-integer max-flow,
  no floating-point tolerance issues) to peel off cores until only
  strictly-homogeneous pieces remain, *then* run Wolfe's algorithm — which
  now never encounters a forbidden-tree marginal, so there's no need to
  detect or recover from the failure mode at all. Implemented and tested:
  `python/src/discrete_modulus/core_deflation.py` +
  `python/src/discrete_modulus/pmf_construction.py`. Column generation
  (§5.1) and a hand-rolled matroid-exchange integer packing (§5.1.5) were
  both explored as alternative/fallback constructions and are **not** used
  in the current design — see §5.1.5 for why.
- **Biggest gap** (admissibility of ρ): v1 accepts the Kruskal-as-untrusted-
  oracle shortcut, with the resulting soundness gap explicitly documented as
  part of the trusted computing base (§3), and a follow-up milestone to close
  it (§5.2, PR6).
- **Reuse [`lean-modulus`](https://github.com/nathan-albin/lean-modulus)**:
  Phase B (§4) leans heavily on infrastructure that already exists there
  (`Multigraph`, `GraphicMatroid`, `FamilyOfObjects`/`Density`/`Adm`) rather
  than rebuilding it — see §4's intro for what's reused vs. new, and the
  recommendation on where this project's Lean code should live. **Better
  news than originally scoped**: Mathlib itself already has general matroid
  restriction/contraction machinery (`Matroid.Minor.Restrict`/`Contract`)
  including the exact "gluing" lemma the deflation-based certificate design
  needs (`Indep.union_isBasis_union_of_contract_isBasis`), proved for *any*
  matroid. A spike proved both the graph-level bridging lemma
  (`Multigraph.isSpanningTree_iff_isBase`) and the certificate's gluing fact
  as thin corollaries — see §4 Phase B and §5.1.5's Lean-mapping note.
  Currently being upstreamed into `lean-modulus` itself (in progress, not
  yet merged — see §4 Phase B's status note).
- **The medium gap's existence fact is *not* sourced from the Fairest Edge
  Usage paper or its matroid generalization** (confirmed: those are
  existence-only for the *fairest* pmf, a stronger/different question than
  ours). See §5.1 for what we actually rely on instead.
- **Certificate format is not yet finalized, and the §6 sketch is known to be
  wrong.** §6's flat "list of (tree, weight) pairs" sketch predates the
  deflation-based design and doesn't fit it: materializing a flat list would
  require an explicit Cartesian product across every deflation level,
  exponential in nesting depth. The current design intent (not yet
  implemented in a certificate format, only in the Python builder's
  in-memory `FactoredPmf`) is a **factored representation that never
  relabels vertices or edges** — a laminar family of vertex-subsets of the
  *original* graph, each with its own small local pmf expressed in original
  edge identities, glued by the matroid restriction/contraction fact above.
  See §5.1.5 and §6 for details and the open schema question.

---

## 1. Goal

Produce, for a given input graph, a **certificate** that a claimed optimal pair
$(\rho^*, \mu^*)$ — admissible density / pmf on spanning trees — is truly
optimal for spanning tree modulus and its blocking dual, checkable by an
independent Lean proof that does not trust the C++ solver's arithmetic.

The duality argument that makes this possible (already derived in
`Certification_Thoughts.md`, §"The duality statement"): for $\rho\in\text{Adm}(\Gamma)$,
$\mu\in\mathcal P(\Gamma)$, Cauchy-Schwarz gives
$1 \le \langle\rho,\eta\rangle \le \|\rho\|\|\eta\|$ where $\eta=\mathcal N^T\mu$; if
equality holds (vectors parallel, $\rho=\eta/\|\eta\|^2$), both are
simultaneously optimal. So the whole verification problem reduces to checking
three things in exact rational arithmetic: (a) $\mu$ is a valid pmf on
spanning trees, (b) $\rho=\eta/\|\eta\|^2$ where $\eta=\mathcal N^T\mu$, and
(c) $\rho$ is admissible ($\mathcal N\rho\ge 1$, i.e. every spanning tree has
$\rho$-weight $\ge 1$).

## 2. Architecture

```
 C++ solver (untrusted, existing)
        │  round-by-round dispatched edge sets
        ▼
 Certificate builder (untrusted, new — Python or C++, "elaborate freely")
        │  versioned certificate: pmf μ on spanning trees (+ derived η, ρ)
        ▼
 Lean verifier (trusted)
   ├─ abstract duality theorem (proved once, graph-independent)
   └─ explicit check: parse certificate, verify (a)/(b)/(c) above in ℚ
```

Nothing upstream of the Lean verifier needs to be correct for the certificate
to be *sound* — only for it to *exist*. This is the standard certifying-
algorithm pattern, and it's why the builder is allowed to be "simple,
untrusted code": bugs there produce a rejected certificate, not a false
"verified" result. The one place this pattern is knowingly relaxed in v1 is
Kruskal-as-oracle (§4, §5.2) — that computation's *result* is trusted, not
just its inputs.

**The "Lean verifier" box is not built from scratch.** `lean-modulus` already
has real, kernel-checked infrastructure that overlaps this box almost
entirely:

| Need | Already in `lean-modulus` | Still to build |
|---|---|---|
| Spanning trees / forests / graphic matroid | `Common/Multigraph.lean`, `Common/GraphicMatroid.lean` — `IsForest`, `IsSpanningTree`, `graphicMatroid`, matroid axioms all proved | Mostly reuse directly. Bonus: `Multigraph` already supports parallel edges, matching the C++ solver's Boost.Graph model, so there's no representation mismatch to paper over. **Addition in progress** (§4 Phase B, §5.1.5): `isSpanningTree_iff_isBase` (bridges `IsSpanningTree` to `Matroid.IsBase`) and `isBase_union_of_isBase_restrict_isBase_contract` (the certificate's gluing fact) — proved in a spike, being upstreamed into `lean-modulus`'s own `GraphicMatroid.lean` rather than kept project-local, since both are general facts about objects that file already owns. |
| Densities, `Adm(Γ)`, the usage pairing | `Common/FamilyOfObjects.lean` — `Density`, `Density.length`, `FamilyOfObjects.Adm`, convexity/closedness | Defining spanning trees as a specific `FamilyOfObjects` (usage vectors), and $\mathcal P(\Gamma)$ (pmfs on Γ) and $\mathcal N^T$ — not yet present. |
| Weak duality | `Common/Duality.lean` proves `one_le_length` — but via the Fulkerson-dual/extreme-points/Krein-Milman route, built for the general theory, not this certificate's shape | Our certificate's duality step is the *simpler* direct Cauchy-Schwarz argument from `Certification_Thoughts.md` — recommend a small, self-contained lemma over reusing this machinery (see §4, PR 4). |
| The medium gap's pmf construction | Existence-only results in the Fairest Edge Usage / matroid-bases literature — confirmed **not** directly reusable (see §5.1) | The pmf construction itself is fully untrusted, fully outside Lean (deflation + Wolfe's minimum-norm-point algorithm, §5.1.5). **Revised from the original "no Lean theory needed" claim**: the *factored* certificate this now produces (§5.1.5) needs a small amount of Lean-side theory to justify gluing independently-chosen local trees into a genuine spanning tree — but this turned out to already exist in Mathlib as a general matroid fact (`Indep.union_isBasis_union_of_contract_isBasis`, any matroid, no graph-specific argument), confirmed via a working spike (§4 Phase B). Still no *new* mathematical theory needed, just wiring — but not literally zero Lean work as originally scoped. |

This changes Phase B (§4) substantially from a from-scratch build to mostly
"wire up the existing pieces plus a few new bridging definitions."

## 3. Trusted computing base (TCB) ledger

Keep this table current as the project proceeds — it's the honest answer to
"what would have to be broken for a bad certificate to verify."

| Component | Trusted? | Notes |
|---|---|---|
| Lean 4 kernel + Mathlib axioms | Yes | Standard, unavoidable. |
| `lean-modulus` `Common/` definitions and proofs (pinned commit) | Yes, but low-risk | The *proofs* (matroid axioms, rank-nullity, etc.) are kernel-checked regardless of which repo they live in — reusing them adds no new trust beyond Mathlib. The *definitions* (`IsSpanningTree`, `Adm`, ...) carry ordinary formalization-adequacy risk: worth a manual sanity check that they mean what we intend, same as any definition we'd write ourselves. Pin the exact commit relied on (§4) so this entry stays auditable. |
| The duality theorem's Lean proof | Yes (by construction) | Proved once, checked by the kernel — a small new lemma (§4, PR 4), not routed through `Duality.lean`'s heavier machinery. |
| Certificate parsing / arithmetic checks in Lean | Yes (by construction) | This is the "explicit verification" — all in ℚ. |
| Kruskal implementation used for ρ-admissibility (v1) | **Yes, unproven** | The accepted gap — see §5.2. Its *output* is trusted without a correctness proof. |
| C++ solver | No | Only a source of candidate certificates. |
| Certificate builder | No | Same — untrusted, can be sloppy/buggy without compromising soundness. |

The single non-standard TCB entry to keep visible everywhere (README, PR
descriptions, verifier's own output banner): *"v1's admissibility check for ρ
relies on an unverified Kruskal implementation."*

## 4. Roadmap

### Phase 0 — ASFW in the Python codebase + a book chapter

Added ahead of Phase A: build and understand the algorithm as its own
standalone piece of the `python/` package before it becomes load-bearing
plumbing inside the certificate builder. Rationale (yours): (1) forces
working through the algorithm's mechanics firsthand; (2) gives a natural,
low-stakes place to tune performance — directly relevant, since §5.1 already
identified an $O(r^3)$-per-minor-cycle scaling bottleneck in Wolfe's full
algorithm; (3) it's needed for PR 2 anyway, so building it standalone means
PR 2 just imports a finished, tested module rather than building it inline;
(4) first-class tests/examples verifying "finds a sparse optimal pmf" as a
property in its own right, independent of the certification-specific
plumbing around it.

**Dependency note — Phase 0 is not a single blocking gate; its two pieces
have different (weaker) dependencies than "do this first" suggests:**
- The **book chapter is not blocking anything**, ever — not Phase A, not
  Phase B, not even the `min_norm_point.py` implementation it describes.
  Drafting it — and the worked examples that go with it — is a genuinely
  good way to build understanding of the algorithm (goal (1)) in parallel
  with implementation work, not necessarily after it finishes. Open its PR
  and iterate on it whenever, alongside everything else.
- **`min_norm_point.py` + its tests block PR 2 only.** Phase A (PR 1: pure
  C++ solver instrumentation) and Phase B (PR 3/PR 4: Lean scaffolding,
  bridge definitions, the certificate-optimality lemma) don't touch the
  pmf-construction algorithm at all and can proceed fully in parallel with
  Phase 0, not sequentially after it. Only PR 2's own work needs to wait on
  Phase 0's Python module being ready.
- Net effect: there's no reason to sit on Phase A/B waiting for Phase 0 to
  "finish" — the only real ordering constraint in the whole plan is
  PR 2 before PR 5 (the verifier needs a certificate format to parse) and
  Phase 0's Python module before PR 2 (PR 2 imports it).

**Scope decision (yours):** implement *and compare* both algorithms in the
away-step Frank-Wolfe family, rather than committing to one:
- **Classic away-step Frank-Wolfe (AFW)** — Guélat & Marcotte 1986: each
  iteration picks a forward direction (MST) *or* an away direction (arg max
  over the current active set), with a closed-form line search along that one
  direction. $O(r)$ per iteration. Not yet prototyped anywhere in this
  project — needs a fresh implementation.
- **Wolfe's (1976) full minimum-norm-point algorithm** — the one already
  validated throughout this conversation (`scratch/wolfe_min_norm_exact.py`):
  full affine-hull projection of the active set each minor cycle, with corral
  eviction. $O(r^3)$ per minor cycle — port the existing prototype rather
  than starting over.
- Run both against the same test graphs (house, $K_n$ at a few sizes, and a
  real multi-round shrunk graph once one is available) and let the numbers
  decide which one PR 2 actually uses — this resolves, before PR 2 depends on
  it, the open question of whether AFW's cheaper per-iteration cost avoids
  the $O(n^4)$-ish blowup seen with Wolfe's full algorithm on $K_{50}$ and on
  `examples/nested`.
- **Resolved: Wolfe's algorithm, not AFW.** Both were implemented
  (`python/src/discrete_modulus/min_norm_point.py`,
  `min_norm_point_afw`/`min_norm_point_wolfe`) and tested
  (`python/tests/test_min_norm_point.py`). The question above turned out to
  have a sharper answer than "which one scales better": AFW's cheaper
  per-iteration cost is real, but irrelevant, because AFW **cannot run to
  completion in exact arithmetic** on any scenario that actually needs its
  away-step mechanism. Its line-search step size $\gamma$ is a "generic"
  rational number every iteration, and rescaling every active weight by
  $(1\pm\gamma)$ compounds denominators multiplicatively with no reduction —
  unlike Wolfe's minor cycle, which re-derives the active set's exact
  barycentric coordinates from a small *integer* Gram matrix each time
  (empirically bounded, matching theory: denominators stayed exactly $|C|$
  in the earlier $K_n$ testing). Confirmed three independent ways while
  building Phase 0: (1) seeding AFW with a single known-forbidden tree
  (weight 1) blew up to 50+ digit numerators/denominators by iteration 7
  with no sign of converging; (2) an isomorphic relabeling of the plain
  house graph (different networkx tie-breaking) hit the same blowup on a
  *cold* start once it needed more than ~7 iterations; (3) a systematic
  sweep of hand-picked two-tree initial active sets (a known-good tree mixed
  with a known-forbidden one, at 19 different weight ratios) never found a
  combination where the away branch triggered without the run already being
  deep enough to be blowing up. AFW's cold start stays cheap and exact where
  it converges in a handful of iterations (validated on house, $K_4$) — the
  implementation and its cold-start tests are kept as a validated comparison
  point — but nothing downstream should call it. **PR 2 uses
  `min_norm_point_wolfe` specifically**, not "whichever the comparison
  recommends" (see PR 2's checklist below).

**Grounding in the existing codebase** (this isn't starting from scratch —
it plugs into an established pattern):
- `python/src/discrete_modulus/algorithms.py`'s `modulus()` is already "the
  incremental basic algorithm that grows the constraint set one object at a
  time via a `ShortestObjectFinder`" — the cutting-plane algorithm this whole
  project keeps drawing on. `families/networkx_families.py`'s
  `MinimumSpanningTree` already implements that protocol for spanning trees —
  reuse it as the forward-direction oracle rather than reimplementing MST
  lookup.
- [x] Check whether `protocols.py`'s `ShortestObjectFinder`/`SubproblemSolver`
      need extending (e.g. a maximum/negated-weight variant for the away-step
      direction) or whether existing min-based finders plus weight negation
      already suffice. **Resolved: existing finders suffice, no extension
      needed.** Away-step FW's away direction is an argmax over the
      *current active set* (a handful of already-visited vertices held in
      memory), not a call through the family's oracle — so `MinimumSpanningTree`
      (the min-based forward oracle) is the only oracle either algorithm
      needs. Separately, `protocols.py` gained `ExactArray` (a
      `dtype=object` numpy array type, generalizing `ShortestConnectingPath`/
      `MinimumSpanningTree`/`SumShortest` to exact `Fraction` arithmetic via
      a one-line dtype fix each) — unrelated to the away-step question, but
      required for either algorithm to run exactly.
- [x] New module, `python/src/discrete_modulus/min_norm_point.py`, implementing
      both variants above (`min_norm_point_afw`, `min_norm_point_wolfe`,
      sharing a `MinNormPointResult`/`SupportEntry` result type). Exact
      rational arithmetic throughout, consistent with
      `spanning_tree_modulus.py`'s existing exact-arithmetic ethos — Wolfe's
      minor cycle ports the `Fraction`-based Gaussian elimination from the
      scratch prototype.
- [x] New tests, `python/tests/test_min_norm_point.py`, porting the properties
      validated in this conversation into first-class pytest cases: house
      graph (and $K_4$) converge to exactly uniform marginals; support
      excludes both of the two combinatorially-forbidden trees (ground truth
      now computed independently per-test via `scipy.optimize.linprog`,
      rather than hardcoded, since `demo.house_graph()`'s edge labeling
      differs from the scratch prototype's); a forced-bad-start test confirms
      the seeded forbidden tree gets evicted. **Wolfe-only for the
      forced-bad-start test** — AFW is excluded there for the exact-arithmetic
      blowup reason above, not an oversight (see `min_norm_point_afw`'s
      docstring). Reuses `demo.house_graph` per existing test-suite
      convention.
- [ ] Performance comparison harness, **Wolfe-only now that AFW is ruled
      out** — no longer an AFW-vs-Wolfe comparison, just Wolfe's algorithm's
      own scaling validation (timing + iteration counts) against $K_n$ and a
      real multi-round shrunk graph, per the open validation task in §5.1.

**Book chapter:** new `.qmd` in `book/`. Suggested (not decided) home:
"Modulus Basics," as a sibling to `The_Basic_Algorithm.qmd` — same "how do
you compute modulus when the object family is too large to enumerate"
motivation, but from the dual/min-norm-point angle rather than the primal
cutting-plane one; "Case Studies," tied specifically to spanning trees, is
the other reasonable fit. Content: the Frank-Wolfe/conditional-gradient
derivation (minimize $\|x\|^2$ over $\text{conv}(\Gamma)$ given a
linear-minimization oracle), why vanilla fixed-step Frank-Wolfe zig-zags on
low-dimensional faces, how the away-step and full-corral fixes differ, a
worked example on the house graph (reusing `demo.house_graph`, matching the
existing chapters' live-executable-code style), and a forward pointer to the
certification use case — written so it stands alone, no Lean/certification
background required to follow it.

**Downstream effect:** PR 2 (below) is revised to *reuse*
`min_norm_point_wolfe` from `min_norm_point.py` rather than implement column
generation or Wolfe's algorithm inline.

### Phase A — Data & untrusted tooling (no Lean; can start immediately)

**PR 1: Solver instrumentation — done, merged to `main`**
- [x] Add an opt-in (flag or new function, not a behavior change to existing
      callers) mode to `spanning_tree_modulus` (`cpp/include/discrete_modulus/cunningham.hpp`)
      that records, per round of the main loop, the `crit_set` dispatched
      together with the component structure it was carved from.
      `solver_trace.hpp` (new); `cunningham.hpp`'s `spanning_tree_modulus`
      takes an optional `SolverTrace*` (default `nullptr`, no behavior change
      for existing callers).
- [x] Define a versioned "solver trace" format (JSON; `"version": 1` field
      from day one). Content per round: the component's vertex set,
      `crit_set`, and `theta`.
- [x] Round-trip test: replaying the trace reproduces the same `eta_star` map
      the normal code path returns, on `examples/house` and `examples/nested`
      (`cpp/test/test_solver_trace.cpp`).
- [x] No change to `spt_mod`'s default CLI output/format — new opt-in
      `--trace` flag writes a separate `<prefix>.trace.json`.

**PR 2: Certificate builder — architecture revised, see §5.1.5; partially
implemented**
- [ ] New standalone tool (suggest Python, matching the "simple, untrusted
      code" framing and easy interop with the existing `python/` package for
      cross-checking) that consumes a v1 solver trace. **Not started** — the
      pieces below exist as tested library functions
      (`python/src/discrete_modulus/`), not yet wired to actually read a
      solver-trace JSON file end to end.
- [x] Per-round pmf construction on each shrunk multigraph. **Revised from
      the original plan** (see §5.1.5): deflate first
      (`core_deflation.find_core`/`deflation_sequence`), then run
      `min_norm_point_wolfe` independently on each resulting strictly-
      homogeneous piece (`pmf_construction.build_factored_pmf`), rather than
      calling Wolfe's algorithm once on the whole shrunk graph. Column
      generation (§5.1) and a matroid-exchange integer-packing approach
      (§5.1.5) were both explored and are **not** used — see §5.1.5.
- [ ] Implement the global gluing step (compose per-round pmfs into one pmf
      $\mu$ on spanning trees of the original graph). **Partially done**:
      `pmf_construction.FactoredPmf` glues cores *within* one round's shrunk
      graph (exact marginals, validated); gluing *across* rounds (using the
      solver trace's own vertex-identification structure, which is the same
      kind of laminar nesting — see §5.1.5) is not yet implemented.
- [ ] Compute and emit derived quantities: $\eta=\mathcal N^T\mu$ and
      $\rho=\eta/\|\eta\|^2$ (cheap, and removes an entire reconstruction step
      from the trusted Lean side — see §5.1's closing note on this tradeoff).
      `FactoredPmf.marginal()` computes $\eta$ exactly for a single round's
      factored pmf already; not yet extended across rounds or to $\rho$.
- [ ] Define the versioned **certificate** format (separate version number
      from the solver-trace format — they'll evolve independently). **§6's
      sketch is stale** (predates the factored/laminar design) — needs a
      real redesign, see §5.1.5 and §6.
- [ ] Validation harness (independent of Lean): check in the builder's own
      untrusted code that emitted $\mu$'s marginals equal the recorded $\eta$,
      that $\|\rho\|^2\|\eta\|^2=1$, etc. This isn't a substitute for the Lean
      proof but catches builder bugs cheaply, long before a Lean run.
      Partial version exists as test assertions
      (`python/tests/test_pmf_construction.py`), not yet a standalone
      certificate-level check.
- [ ] End-to-end smoke test on `examples/house` and `examples/nested` (small
      enough to eyeball the resulting pmf by hand). Not yet run against a
      real solver trace end to end — `pmf_construction.py` is validated on
      synthetic graphs (house, multi-level house, $K_n$, and a synthetic
      multigraph) only so far.

### Phase B — Lean foundations (can proceed in parallel with Phase A)

**Where should this Lean code live?** Recommendation: a **separate Lean
project** (`discrete-modulus/lean/`) that depends on `lean-modulus` as a
pinned Lake dependency, rather than adding it as a new entry inside
`lean-modulus` itself. Reasoning, open to being overridden:
- `lean-modulus` is organized around formalizing *papers*, with a blueprint
  that tracks paper-statement ↔ Lean-declaration correspondence. This
  verifier isn't formalizing a paper — it's an applied tool that ingests a
  JSON certificate and type-checks a specific numeric instance. Forcing it
  into the blueprint's paper-tracking shape would be awkward (though if the
  new bridging lemmas in PR 4 turn out small enough to fit naturally in an
  "Applications/"-style folder there instead, that's worth reconsidering —
  flagging this as a soft, reversible call, not a hard architectural fork).
- A pinned dependency is arguably *better aligned* with the TCB-ledger
  discipline this whole plan is built on (§3): it makes explicit exactly
  which commit of `Common/`'s definitions the certificate's soundness rests
  on, rather than silently tracking `lean-modulus`'s `main` branch.
- Cost: a cross-repo dependency to bump deliberately when `Common/` changes,
  instead of it happening for free in the same repo. Worth it here given the
  differing purposes above.
- [x] **Confirmed with a throwaway spike.** Pulled `lean-modulus` in as a
      pinned Lake dependency (`rev = "main"`, later fixed to a specific
      commit) and built a file importing `Multigraph`/`GraphicMatroid` plus
      Mathlib's `Matroid.Minor.Contract`/`Minor.Restrict` — dependency
      mechanics (toolchain `v4.32.0-rc1`, Mathlib's pinned commit) work
      cleanly; Mathlib's binary cache download (~8600 files) takes a few
      minutes but no source rebuild is needed. **Went further than the
      mechanics check**: proved two real theorems in the spike (not just
      `sorry`-stubbed statements), described below and in §5.1.5.
      - `Multigraph.isSpanningTree_iff_isBase` — a spanning tree of `G` is
        exactly a base of `G.graphicMatroid`, *given* `G` itself (all its
        edges) is connected. This closes a gap `GraphicMatroid.lean`'s own
        docstring already flagged ("route through `Matroid.IsBase` rather
        than reproving them directly"). The connectivity hypothesis wasn't
        anticipated in earlier design discussion — without it the
        equivalence is false one direction (a maximal forest of a
        disconnected graph is a spanning *forest*, not `IsSpanningTree`'s
        single all-vertex-spanning tree); every shrunk multigraph the
        solver actually dispatches is connected by construction, so this
        isn't a blocker, just a precondition to thread through explicitly.
      - `Multigraph.isBase_union_of_isBase_restrict_isBase_contract` — the
        certificate's "gluing" fact: a spanning tree of one vertex block
        plus a spanning tree of the contracted rest of the graph unions to
        a spanning tree of the whole graph. Proved in ~9 lines, entirely by
        specializing Mathlib's own general
        `Matroid.Indep.union_isBasis_union_of_contract_isBasis` (true for
        *any* matroid, no graph-specific argument needed) — confirming the
        "no new graph theory needed for gluing" hope from the design
        discussion.
      - **Status: merged.** Both lemmas now live in `lean-modulus`'s own
        `Common/GraphicMatroid.lean` on `main`, commit
        `1c91aa7412e0421dc8992c15f0932dda9f8756b2` — pushed from outside
        the Codespace's scoped `GITHUB_TOKEN` (which couldn't push
        cross-repo, as originally noted here) and confirmed directly
        against GitHub. This is the exact commit `lean/lakefile.toml`
        pins (§4 Phase B, PR 3).
      - Reusable throwaway spike project (separate from the PR branch above):
        `scratch/lean_spike/` — a minimal `lakefile.toml` template if this
        needs to be redone or extended.

**PR 3: Lean project scaffolding — done, on branch `spanning-tree-cert`
(not yet merged to `main`)**
- [x] New `lean/` directory: `lakefile.toml`, Lean toolchain matching
      `lean-modulus`'s (`v4.32.0-rc1`), `lean-modulus` pinned as a git
      dependency at the specific commit above (not `rev = "main"`, for
      TCB auditability per §3), CI job (`.github/workflows/lean-test.yml`,
      mirroring `cpp-test.yml`'s shape) that runs `lake build`.
- [x] Landed an import smoke test as the first real file
      (`lean/DiscreteModulusCert/Basic.lean`), adapted from the spike's
      config (`scratch/lean_spike/`, not reused directly, per the original
      plan here). **Differs from the original plan in one way, for the
      better:** since the two lemmas are now upstreamed into
      `lean-modulus` itself rather than living spike-local, the smoke
      test doesn't re-prove them — it just imports
      `LeanModulus.Common.GraphicMatroid` and `#check`s both lemmas by
      name, confirming the pinned commit actually exposes them.
      `lake build` confirmed green (`Build completed successfully`, both
      `#check`s resolve with the expected types) after re-running on a
      bigger Codespace — the original 2-core/no-swap Codespace was CPU-
      starving the build, not failing it (available RAM held steady
      throughout; see `scratch/HANDOFF.md`'s now-resolved diagnosis,
      kept for the record).
- [x] **Decided: keep Lean out of the main devcontainer entirely.** Mathlib's
      binary cache alone is ~8600 files / several minutes / multiple GB —
      real cost on every codespace rebuild for contributors who never touch
      the verifier. Instead: a small setup script under `lean/` (e.g.
      `lean/setup.sh`) that installs `elan` and runs `lake update`/
      `lake exe cache get` on demand, run once by whoever is actually working
      on the Lean side. `.devcontainer/Dockerfile` stays untouched. A
      separate Lean-specific devcontainer variant (VS Code supports multiple
      `.devcontainer/<name>/` configs, and one with Mathlib's cache
      pre-baked into a pushed image would start faster than the script on
      repeat use) is a reasonable later upgrade if Lean work becomes frequent
      enough to justify the extra image/registry maintenance — not worth
      building now. CI (whenever PR 3's `lake build` job lands) installs its
      own `elan`/`lake` in-job, independent of whatever the interactive
      devcontainer looks like. **Implemented**: `lean/setup.sh`.

**PR 4: Bridge definitions + the certificate-optimality lemma — done, on
branch `spanning-tree-cert` (not yet merged to `main`); one scope finding
changes the §6 certificate-schema question**
- [x] **Finding that reshapes this PR: `lean-modulus`'s own
      `Density`/`FamilyOfObjects`/`Adm` (`ℝ≥0`-valued) turned out not to be
      reusable for the optimality lemma at all, not just "vocabulary only"
      as originally scoped.** `ℝ≥0` has no subtraction, and Mathlib's
      finite Cauchy-Schwarz inequality (`Finset.sum_mul_sq_le_sq_mul_sq`,
      confirmed to exist essentially as anticipated below) needs a genuine
      ordered *ring*, so it doesn't apply to `ℝ≥0` directly —
      `lean-modulus`'s own `Common/Duality.lean` works around exactly this
      by detouring through `ℝ` via `Density.toReal` plus real-analysis
      machinery (compactness, extreme points) that this certificate has no
      other use for. Since certificate values are exact rationals
      throughout anyway, the fix was to define a small self-contained
      `ℚ`-native vocabulary from scratch (`CertDensity := E → ℚ`,
      `pairing`, `sqNorm`, `IsAdmissible`/`Adm`, a `Pmf` structure) in the
      new file `lean/DiscreteModulusCert/Family.lean`, reusing only the
      graph/matroid layer (`Multigraph`, `IsSpanningTree`) from
      `lean-modulus`, which doesn't mention densities at all and so isn't
      affected by the `ℝ≥0`-vs-`ℚ` mismatch.
- [x] Defined spanning trees' usage vectors directly (`spanningTreeUsage`,
      the `{0,1}`-indicator of a `Set E` satisfying `IsSpanningTree`) rather
      than through `lean-modulus`'s `FamilyOfObjects` type, per the finding
      above — same mathematical content, just not literally that type.
- [x] Defined `𝒫(Γ)` as `DiscreteModulusCert.Pmf`: a `Finset (Set E)`
      support plus a `Set E → ℚ` weight function, with the three expected
      properties (support elements are genuine spanning trees, weights
      nonnegative, weights sum to `1`). **This is directly relevant to the
      open §6 schema question**: `Pmf`'s shape — a finite list of edge sets
      plus a rational weight each — *is* the shape of a certificate's
      leaf-level local pmf block, and confirms the numeric-type half of §6
      is settled: certificate weights parse straight into `ℚ` literals,
      with no `ℝ≥0`/`NNReal` coercion anywhere in the trusted verifier.
      `𝒩ᵀμ` is `Pmf.marginal`.
- [x] Proved the **certificate-optimality lemma**
      (`DiscreteModulusCert.certificate_optimality`,
      `lean/DiscreteModulusCert/Optimality.lean`), self-contained as
      planned. Went slightly further than the original scope: proves both
      halves of "simultaneously optimal" as two symmetric Cauchy-Schwarz
      corollaries sharing one lemma
      (`Pmf.one_le_pairing_marginal_of_admissible`) — (a) `ρ` minimizes
      `sqNorm` over *every* admissible density (`ρ` solves the modulus
      problem), and (b) `η` minimizes `sqNorm` over the marginals of
      *every* pmf on `G`'s spanning trees (the dual min-norm-point
      problem — literally the quantity Wolfe's algorithm, §5.1, computes).
      The original plan only asked for the informal "both optimal"
      conclusion; formalizing it as two explicit minimality statements
      makes precise what PR 5's verifier is actually allowed to conclude.
      Axiom-checked (`#print axioms`): depends only on `propext`,
      `Classical.choice`, `Quot.sound` — no `sorry`.
- [x] **Decision point, resolved as anticipated:** did not reach for
      Mathlib's `InnerProductSpace` machinery. `Finset.sum_mul_sq_le_sq_mul_sq`
      exists close to the anticipated name/shape
      (`Mathlib.Algebra.Order.BigOperators.Ring.Finset`), stated for any
      `[CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
      [ExistsAddOfLE R]` — `ℚ` satisfies all four
      (`Mathlib.Algebra.Order.Ring.Rat`'s `instIsStrictOrderedRing`), so it
      applies directly with no need to hand-roll the discriminant argument.
      Everything is stated in *squared* form (`pairing f g ^ 2 ≤ sqNorm f *
      sqNorm g`) specifically to avoid `Real.sqrt`/`NNReal.sqrt` anywhere —
      the whole proof stays in `ℚ`, never touches `ℝ`.
- [x] Proved the **admissibility definitional lemma**
      (`isAdmissible_iff_one_le_pairing_spanningTreeUsage`) — genuinely
      `Iff.rfl` as anticipated, kept as a named, discoverable lemma. **Not
      done**, deferred to PR 5: the further equivalence to "the *minimum*
      spanning-tree weight is `≥ 1`" (the form that literally matches a
      Kruskal computation's output) needs the minimum to be attained,
      which needs a Kruskal implementation to exist first (§5.2) — no
      point proving it in the abstract before PR 5 needs the exact shape.
- [x] **Gluing combinator done: `DiscreteModulusCert.Pmf.glue`
      (`lean/DiscreteModulusCert/Glue.lean`).** Composes a block's
      tree-pmf (`μA : Pmf (M ↾ A)`) with the canonical rest-of-graph
      tree-pmf (`μRest : Pmf (M ／ A)`) into one pmf on `M`'s bases
      (product-measure weights, `μA.weight I * μRest.weight J` on
      `J ∪ I`), via `isBase_union_of_isBase_restrict_isBase_contract`. No
      `sorry` (axiom-checked). This required a refactor first (see below),
      and what was originally flagged as an unprovable-without-graph-theory
      gap (`hcompat`) turned out to be a **provable Mathlib-level matroid
      fact** — a real strengthening over the first version of this PR, see
      below.
    - **Refactor: `Pmf`/`IsAdmissible`/`Adm` moved from `Multigraph`
      (`IsSpanningTree`-based) to `Matroid` (`IsBase`-based).** Necessary
      because the gluing fact is stated for `M ↾ A` and `M ／ I` — neither
      is obviously "the graphic matroid of some other multigraph" without
      extra graph theory this project doesn't otherwise need. Working with
      bare `Matroid E` throughout `Family.lean`/`Optimality.lean`/
      `Glue.lean` sidesteps that entirely; the graph-language
      interpretation for the *top-level* pmf (the one `certificate_optimality`
      is invoked on) is a two-line corollary,
      `isAdmissible_graphicMatroid_iff` (`Family.lean`), via
      `isSpanningTree_iff_isBase` given `G` connected. `certificate_optimality`
      itself is unaffected in substance — just restated over `{M : Matroid E}`
      instead of `{G : Multigraph V E}`, which if anything is more honest
      (it's really a fact about any matroid's base polytope, not
      graph-specific — consistent with the plan's own earlier observation
      that this problem is a submodular-minimization special case, §5.1).
    - **`hcompat` upgraded from an assumed hypothesis to a proved theorem,
      `isBase_contract_iff_of_isBasis_restrict` (`Glue.lean`).** The
      gluing fact needs `J` to be a base of `M ／ I` for the *specific*
      `I` drawn from `μA` — a priori a different matroid per `I`. The
      first version of this PR took as a hypothesis the informal graph
      fact "shrinking a block to a point is about which vertices merge,
      not which spanning tree justified it, so `M ／ I` and `M ／ I'` have
      the same bases outside the block for any two block-bases." It turns
      out this **is** a general matroid fact, with no graph-specific
      argument needed, provable directly from two pieces already in
      Mathlib: `IsBasis'.contract_eq_contract_delete` (contracting by a
      set equals contracting by one of its bases, then deleting the rest
      of the set) plus the fact that the deleted elements are all loops of
      the smaller contraction (so deleting them doesn't change which
      *disjoint* sets are bases — `Matroid.IsBase.isBasis_of_subset` and
      `Matroid.IsBasis.isBase_of_spanning` do the rest). **Consequence:**
      `Pmf.glue` no longer takes `hcompat` as a parameter at all — `μRest`
      is now typed directly as `Pmf (M ／ A)` (contraction by the whole
      block, canonical, no tree-dependence), and compatibility with
      whichever tree of the block gets drawn is derived automatically
      inside `isBase`'s proof. This closes what would otherwise have been
      a real, if narrow, soundness gap: an assumed (not verifier-checked)
      hypothesis inside the trusted certificate-optimality machinery. The
      one remaining hypothesis, `hdisj` (`μRest`'s trees never touch the
      block's edges at all), is fully decidable/computable directly from
      concrete certificate data (a finite disjointness check), so it's
      genuinely verifier-checkable, unlike `hcompat` would have been (a
      universally-quantified matroid statement, not brute-forceable at
      realistic graph sizes).
    - **What this means for gluing across the whole laminar family, not
      just one restrict/contract split (investigated, not yet
      implemented):** read `python/src/discrete_modulus/pmf_construction.py`
      and `cpp/include/discrete_modulus/solver_trace.hpp` directly (rather
      than re-deriving from this doc's prose) to check how `Pmf.glue`
      composes over a *whole* laminar family, not just one split. Finding:
      **both the within-round core-deflation nesting and the
      across-round `crit_set` nesting reduce to the same flat, ordered
      structure** — `build_factored_pmf`'s `pieces: list[LocalPiece]`
      is built in strict discovery order, each piece's own edges disjoint
      from all earlier ones (confirmed via its docstring: "the pieces
      partition `G`'s edges"), and `SolverTrace.rounds` is likewise a flat
      list of rounds each dispatching a `crit_set` disjoint from every
      other round's. Working through the matroid restriction/contraction
      composition confirms this isn't a coincidence: processing pieces in
      discovery order, the ambient matroid at step `i` is
      `M ↾ (A_1 ∪ ⋯ ∪ A_i)`, restriction composes
      (`(M ↾ X) ↾ Y = M ↾ Y` for `Y ⊆ X`) so the "already-glued" pmf from
      step `i-1` is exactly `Pmf (M ↾ (A_1∪⋯∪A_i) ↾ (A_1∪⋯∪A_{i-1}))`
      — precisely `Pmf.glue`'s `μA` argument — and this holds regardless
      of whether piece `i` came from deflation or from a later solver
      round, since both are the same "restrict then contract" operation.
      **Consequence for §6:** the whole multi-round, multi-core
      certificate reduces to *one flat ordered list* of pieces (round 1's
      pieces, then round 2's, …), verified by a single left-fold of
      `Pmf.glue` — not a tree with parent pointers as originally sketched.
      See §6's rewrite for the schema this implies.
    - **Fold driver: now done** (`PieceList`/`PieceList.glueAll`,
      `Glue.lean` — see §6's rewrite for the details and what's still
      open). **Still not implemented:** the certificate *parser* that
      produces a `PieceList`'s inputs from raw JSON — per-piece `IsBase`
      proofs in particular, §6's main remaining item, real PR 5/Phase C
      work.

### Phase C — Verifier & integration

**PR 5: Certificate ingestion + explicit verification**
- [ ] Parser for the PR 2 certificate format into the PR 4 Lean types (all
      rational arithmetic — no floating point anywhere in this repo's Lean
      code).
- [ ] Verify $\mu$ is a valid pmf on the spanning trees it claims to use
      (nonneg weights summing to 1, each support element actually a spanning
      tree of the input graph).
- [ ] Reconstruct $\eta$ from $\mu$ inside Lean and check it matches the
      certificate's claimed $\eta$ (or skip reconstruction and just trust the
      builder's $\eta$/$\rho$, re-deriving $\eta$ from $\mu$ *only* — cheaper,
      and still sound, since $\eta$ is fully determined by $\mu$; decide which
      based on how expensive kernel-level rational arithmetic on the full
      pmf turns out to be).
- [ ] Check $\rho = \eta/\|\eta\|^2$ exactly in ℚ.
- [ ] Admissibility of $\rho$: run the (unproven) Kruskal implementation,
      check its output weight $\ge 1$. **Prominently log/print that this
      step relies on an unverified component** — this should be visible in
      the verifier's own final output, not just in this planning doc.
- [ ] Wire PR 4's certificate-optimality lemma to these facts to conclude
      optimality; the verifier's final output is a Lean term whose
      type-checking is the whole point.
- [ ] End-to-end test: `house`/`nested` traces all the way through solver →
      builder → Lean, `lake build`/kernel accepts.

**PR 6 (follow-up, not blocking PR 5): prove Kruskal correct, close the TCB gap**
- [ ] Prove the greedy-exchange argument for Kruskal on the graphic matroid
      in Lean (this is the actual "hard Lean project" — matroid greedy
      theorem specialized to graphs), concluding Kruskal's output *is* a
      minimum spanning tree, not just trusted to be.
- [ ] Swap this proof into PR 5's admissibility check, removing the last
      unproven-external-computation entry from the TCB ledger (§3).
- [ ] This can be scoped as its own PR (or its own small stack) independent
      of everything else — nothing in Phases A/B/C blocks on it, and nothing
      needs to be re-architected when it lands.

## 5. The two flagged gaps

### 5.1 Medium gap — constructing the per-round pmf (Wolfe's minimum-norm-point algorithm)

**Revised twice now (see below): the peeling algorithm originally sketched
here was replaced by column generation, which is now itself superseded as the
*featured* recommendation by a better-fitting algorithm — Wolfe's (1976)
minimum-norm-point method — identified via your own "Plus-1 algorithm."**
Column generation (kept below, still valid, still a fine fallback) treated
this as a generic LP-feasibility problem. Wolfe's algorithm is a closer match:
it's the established, specialized fix for exactly the failure mode ("adding a
forbidden tree, having to wash it out") your own algorithm was already
running into, and it directly answers both questions you raised about it.

**Your "Plus-1 algorithm" identified precisely.** Initializing $w_0=0$ and
repeatedly setting $w_{k+1}(e) = w_k(e) + \mathbb 1_{\gamma_k}(e)$ for
$\gamma_k=\arg\min_\gamma\langle w_k,\gamma\rangle$ (an MST under the current
weights) is exactly **vanilla Frank-Wolfe / conditional-gradient descent**
minimizing $\|x\|^2$ over $\text{conv}(\Gamma)$, using a *fixed* step size
$1/(k+1)$: writing $x_k=w_k/k$, $x_{k+1} = \frac{k}{k+1}x_k +
\frac{1}{k+1}\mathbb 1_{\gamma_k}$ is precisely that recursion (positive
rescaling doesn't change an argmin, so weighting by $w_k$ or $x_k$ picks the
same tree). That's why $w_k/k\to\eta^*$ — $\eta^*$ *is* the min-norm point of
$\text{conv}(\Gamma)$ — and it explains the slow, oscillating convergence
precisely: fixed-step Frank-Wolfe is provably only $O(1/k)$, and it's a
**well-documented, named phenomenon** (not a bug in your reasoning) that
vanilla Frank-Wolfe *zig-zags* when the minimizer lies on a low-dimensional
face of the polytope (Guélat & Marcotte, 1986) — exactly this situation,
since $\eta^*$ is highly degenerate, supported on a handful of vertices out of
exponentially many. "Adding a forbidden tree, then the linear growth of $w_k$
has to wash away that mistake" *is* that zig-zag.

**Answering your two questions directly, with an established fix rather than
a new one:**
- *"Is there a way to recognize a bad tree and back up?"* — Yes:
  **away-step Frank-Wolfe** (Guélat & Marcotte 1986; rigorized/popularized by
  Lacoste-Julien & Jaggi 2015) explicitly tracks an active set and, each
  iteration, also considers *removing* weight from the currently-worst active
  vertex rather than only adding to a new one. I implemented the fuller
  version — **Wolfe's 1976 minimum-norm-point algorithm** — which maintains an
  active set ("corral") with an explicit eviction rule: project onto the
  affine hull of the current active set, and if any point's affine
  coefficient goes negative, evict it. This is also the algorithm underlying
  **Fujishige's minimum-norm-point method for submodular function
  minimization** — matroid rank functions (e.g. the graphic matroid here) are
  submodular, so this problem is a direct special case of that literature, not
  just an analogy.
- *"Does it converge in finitely many iterations once bad trees are
  avoided?"* — On the house graph, Wolfe's algorithm converged in **3 major
  iterations, 2 minor iterations, 0 evictions** from a cold start. To test the
  eviction mechanism directly, I forced the initial active set to contain one
  of the two known-forbidden trees: it converged in **4 major, 4 minor
  iterations, 1 eviction** — and the eviction log confirmed the evicted tree
  was exactly the forbidden one. Both runs land on a valid 3-tree support
  avoiding both forbidden trees, marginals exactly $2/3$ (checked via
  `Fraction`). This isn't a general "any smooth objective converges finitely"
  guarantee — it's specifically that Wolfe's algorithm is the established,
  widely-used, empirically-fast/finite tool for *this* problem shape (min-norm
  point of a polytope from a linear-minimization oracle), which is why it's
  worth featuring over a generic LP formulation.

Prototype: `scratch/wolfe_min_norm.py`. Column generation (below) remains a
validated fallback if Wolfe's algorithm's scaling behavior turns out worse in
practice — see the shared open validation task after both are described.

**Setup.** At one round, the solver dispatches edge set $C$ (`crit_set`,
[cunningham.hpp:386-392](../cpp/include/discrete_modulus/cunningham.hpp#L386-L392)),
splitting the current component into $|\tilde V|$ pieces
([cunningham.hpp:404](../cpp/include/discrete_modulus/cunningham.hpp#L404)), with the
invariant (already asserted in the existing code,
[cunningham.hpp:405](../cpp/include/discrete_modulus/cunningham.hpp#L405)):
$\theta = (|\tilde V|-1)/|C|$. Shrinking each piece to a vertex gives
$\tilde G=(\tilde V, C)$. We want a pmf on spanning trees of $\tilde G$ giving
every edge of $C$ marginal usage exactly $\theta$.

**Existence — and why the Fairest Edge Usage paper isn't the shortcut it
looks like.** At first glance this "uniform-marginal pmf on spanning trees"
question looks like exactly what "Fairest Edge Usage and Minimum Expected
Overlap for Random Spanning Trees" (and its matroid generalization, Truong &
Poggi-Corradini) is about — but per your answer, those results are
existence-only for the *fairest* (min-overlap) pmf among all pmfs achieving a
prescribed marginal, which is a strictly harder, different question than "does
*any* pmf achieving this marginal exist, and can we build one." So that
literature isn't the source for either half of this gap — don't spend time
trying to port its proof.

What we actually need for existence: the uniform vector $x_e=\theta$ for
$e\in C$ lies in the spanning-tree (matroid base) polytope of $\tilde G$
exactly when, for every $F\subseteq C$, $x(F)=\theta|F|\le\text{rank}(F)$ —
i.e. no subset of $C$ is denser than $C$ itself. That's precisely what it
means for $C$ to be *the* tight/critical set the solver extracted at this
round, which is a fact about Cunningham's algorithm itself (Albin, Kottegoda,
Poggi-Corradini, the paper this C++ code implements) — so existence should
already follow from that paper's own correctness proof, restated as a lemma,
not new theory. Given that, Carathéodory's theorem for polytopes says $x$ is a
convex combination of at most $\dim(\text{base polytope})+1\le|C|$ vertices,
i.e. spanning trees — matching the "no more than $|C|+1$" bound in
`Certification_Thoughts.md`.

#### Fallback: column generation

**Construction — column generation.** Variables $\lambda_T\ge0$, one per
spanning tree of $\tilde G$ (exponentially many, never enumerated). Constraints:
$\sum_T \lambda_T\,\mathbb 1_T(e) = \theta$ for each $e\in C$, and
$\sum_T\lambda_T = 1$. Solve via Phase-1 simplex with an explicit artificial
variable per constraint (minimize $\sum(\text{artificials})$), starting from an
empty working set of trees:

```
working_set ← {T0}                      # any one spanning tree, to bootstrap
loop:
    solve the small Phase-1 LP restricted to working_set (+ artificials)
    if Phase-1 objective == 0: return the (sparse) support — done
    y ← dual prices (shadow prices) on the restricted LP's equality rows
    T ← the spanning tree maximizing Σ_{e∈T} y_e     # max-weight spanning tree
                                                       # w.r.t. weights y — a
                                                       # Kruskal-type computation
    if T already in working_set: stall (shouldn't happen away from optimum)
    working_set ← working_set ∪ {T}
```

The pricing step — "which tree would most help feasibility right now" — is a
**maximum-weight spanning tree computation against the current LP dual
prices**, exactly analogous to the "most violated constraint" step in the
book's basic algorithm (that one polls a min/max-weight-spanning-tree oracle
against the current primal density; this one polls the same kind of oracle
against the current dual prices). Either way, the oracle is cheap (Kruskal),
not a submodular-minimization search — this fully replaces the peeling
sketch's open question about computing $\lambda$.

**Validated on the house graph (column generation specifically).** I ran it on
`examples/house`: `spt_mod examples/house` confirms
the whole graph is processed in a single round (`crit_set` = all 6 edges,
$\theta=2/3$, matching `examples/house.eta` where every edge — including the
chord — gets $2/3$), so $\tilde G$ *is* the house graph here.

- Brute-force LP check over all 11 spanning trees confirms **exactly two**
  can never appear in any feasible pmf's support — precisely the claim in
  your message. (Both omit an edge incident to vertex 0, the unique vertex not
  touching the chord — not an obvious pattern from staring at the graph, which
  is exactly why this needed checking computationally rather than assumed.)
- Column generation converges in **5 iterations** to a **3-tree support**
  (weights $1/3, 1/3, 1/3$) — sparser than the $\le 6$ Carathéodory bound —
  and **never touches either forbidden tree**. Re-verified with exact `ℚ`
  arithmetic (`fractions.Fraction`, no floating-point residue): all 6 marginals
  land on exactly $2/3$, weights sum to exactly $1$.
- Also implemented an **exact-arithmetic version of the whole loop** (not just
  the final check) using `cdd.gmp` (pycddlib's GMP-backed exact LP solver,
  `scratch/column_gen_exact.py`) — on house this actually did *better*,
  converging in **2 iterations**, exact throughout, no separate verification
  pass needed. See the exactness note below for why this doesn't generalize
  to bigger instances.

**Stress-tested for scaling (column generation) — results are honest, not
uniformly rosy.** On complete graphs $K_n$ (a legitimate stand-in for a
shrunk graph: by vertex-transitivity the uniform vector is provably the
unique target, so it's a valid test case without needing a real solver
trace), the algorithm always terminates and is always correct, but for
$n=10,15,21,30$ it converged to support size *exactly* $|C|$ (the naive
worst-case Carathéodory bound), not something sparser like house's
3-out-of-6. This is very likely an artifact of $K_n$'s enormous symmetry
group causing massive tie-breaking degeneracy in naive pricing (a known
failure mode of vanilla column generation on highly symmetric instances —
e.g. $K_{2k+1}$ actually decomposes into just $k$ edge-disjoint Hamiltonian
cycles, so a *much* sparser $O(n)$-tree solution provably exists; naive
pricing just doesn't find it without smarter tie-breaking or exploiting that
structure). Real shrunk graphs from the solver are extremely unlikely to have
$K_n$'s automorphism group, so this shouldn't generalize, but it's untested
on real (non-toy) data.

**Wolfe's algorithm has *not* yet been through the same $K_n$ stress test** —
only validated on house so far (cold start and forced-eviction, both above).
Given away-steps/eviction are specifically the mechanism vanilla Frank-Wolfe
lacks and $K_n$'s degeneracy is exactly a "many ties, no clear improving
direction" scenario, there's real reason to expect Wolfe's algorithm handles
$K_n$ better than plain column generation did — but that's a hypothesis, not
yet a finding. Both algorithms need the same real-data validation:
- [ ] **Open validation task (applies to both algorithms):** run whichever
  algorithm(s) are chosen against a real multi-round shrunk graph once PR 1's
  instrumentation exists (`examples/nested` decomposes over 3 rounds — `1/2`
  then `1/4` then `1/10`, with `crit_set` sizes 40/80/190 — a good
  non-symmetric stress test), and separately run both against $K_n$ for
  larger $n$ to compare their scaling head-to-head. I attempted to extract a
  real shrunk graph early by hand-porting
  `solve_subproblem`/`cunningham_min`/`graph_vulnerability` to Python
  (networkx max-flow) rather than waiting for PR 1, and hit a bug (the ported
  max-flow under-counts achievable weight) I didn't chase down — not worth
  debugging a throwaway port when PR 1 gives the real thing directly. Don't
  skip this validation; house is too small/simple to be reassuring on
  its own about the *worse* end of the scaling question.
- [ ] **Performance caveat, not a soundness one:** the prototype re-solves the
  whole restricted LP from scratch every iteration (simplest to write); this
  took 122s for $K_{30}$ ($|C|=435$). A real implementation needs a proper
  warm-started/revised-simplex column-generation loop (updating the basis
  incrementally, standard practice for column generation), not a from-scratch
  resolve each round — this is an implementation-quality fix, not evidence
  against the approach.

**No new Lean theory needed for this gap at all, regardless of which
algorithm builds the pmf.** Because this whole construction lives in the
untrusted certificate builder (PR 2), the Lean verifier (PR 5) never needs to
know *how* the pmf was found — it only checks the final claimed
$(\text{trees}, \text{weights})$ list's marginals arithmetically, which was
already scoped and needs no polytope/Carathéodory/LP-duality/Frank-Wolfe
theory in Lean. This also **sidesteps** the earlier open question about
whether $C$ has a proper tight subset (previously flagged as needing
verification before picking an algorithm) — neither Wolfe's algorithm nor
column generation cares either way; both find a feasible decomposition
regardless of whether $\tilde G$ is further reducible.

**On "what else to compute" (from the thoughts doc):** yes, worth having the
builder emit $\eta$ and $\rho$ directly (PR 2's task list already reflects
this) — it's free in untrusted code and lets PR 5's verifier choose the
cheaper option of re-deriving $\eta$ from $\mu$ and just checking equality,
rather than reconstructing everything from raw per-round data inside the
kernel.

**Exactness note for PR 2 — checked `pycddlib`/`cdd.gmp` as an alternative to
the floating-point-then-reverify split, verdict: not as the inner-loop
solver.** `pycddlib` is already a project dependency (used elsewhere for
polyhedron enumeration in the book's examples) and its `cdd.gmp` submodule
(distinct from the default `cdd` module, which silently accepts `Fraction`
inputs and converts them to floats — easy to get burned by if you don't check)
does genuine GMP-backed exact-rational LP solving, ruling out any need to
handle floats at all. On house it worked *better* than the scipy/HiGHS
version (2 iterations vs. 5, exact throughout). But stress-testing it the same
way as the floating-point version (§ above): running the same $K_n$ scaling
check with `cdd.gmp` as the inner-loop solver, $K_{10}$ ($m=45$, the
*smallest* case tested, which scipy/HiGHS solved in 0.15s) still hadn't
converged after 6.5 minutes of CPU time — had to be killed. Two compounding
causes, not just "exact arithmetic has overhead": (a) the prototype rebuilds
the whole restricted LP from scratch every iteration regardless of solver,
and every arithmetic op in that rebuild costs far more under GMP rationals
than hardware floats; (b) `cdd`'s LP solver is a much simpler implementation
than HiGHS — its primary purpose in this codebase is polyhedron vertex/facet
enumeration (the *already-known-impractical-past-tiny-graphs* operation noted
elsewhere in the book), with LP-solving very much secondary, not a
competitively tuned simplex implementation.

**Recommendation for column generation specifically, unchanged in substance:**
run it in floating point (scipy/HiGHS or similar — mature, fast,
warm-startable) to discover *which* small set of trees form the support, then
re-solve only the small *final* linear system (weights over the now-fixed
support, $\le|C|+1$ unknowns) exactly in `ℚ` before emitting the certificate —
either plain `Fraction`-based Gaussian elimination or `cdd.gmp` are fine for
that final step specifically, since by then it's a small, one-shot solve, not
a from-scratch resolve repeated dozens of times. Floating-point column
generation picking a bad support just means a wasted attempt (the builder is
untrusted anyway), but the certificate itself must be exact or PR 5's verifier
correctly rejects it.

**Wolfe's algorithm doesn't need this float-then-exact split at all — it can
run exactly throughout, and it's cheap enough to actually do so.** Since we
know a priori that $\eta^*$'s (and hence the pmf weights') denominators
divide $|C|$, I tried running the *entire* algorithm — including the minor
cycle's affine-projection step — in exact `fractions.Fraction` arithmetic
(`scratch/wolfe_min_norm_exact.py`), replacing every floating-point tolerance
check (`> tol`, `>= x - tol`) with true exact `>`/`>=`. This is *not* the same
situation as the `cdd.gmp` column-generation attempt above: Wolfe's minor
cycle only ever solves a small $(r{+}1)\times(r{+}1)$ linear system ($r$ =
current active-set size), not a growing general LP with $O(m)$ artificial
variables rebuilt from scratch — a fundamentally cheaper exact computation,
via a hand-rolled exact Gaussian elimination (no external LP library needed).

- **House graph:** exact match to the floating-point version's behavior on
  both the cold start (3 major/2 minor, 0 evictions) and the forced-forbidden
  start (4 major/4 minor, 1 eviction, confirmed evicting exactly the forbidden
  tree) — but now provably exact, weights landing on exactly `Fraction(1,3)`,
  denominator exactly `3` (dividing $|C|=6$ as predicted), no epsilon anywhere.
- **$K_n$ scaling — genuinely better than either prior attempt, with one
  caveat to fix before relying on it at scale:** support size tracked $n$, not
  $m$ (10 trees for $K_{10}$, 50 for $K_{50}$ — much closer to the true sparse
  optimum than column generation's worst-case $m$-sized support on the same
  instances), and it's dramatically faster than `cdd.gmp` — $K_{50}$
  ($m=1225$) finished in 93.5s, versus `cdd.gmp` not finishing $K_{10}$
  ($m=45$) in 6.5 minutes. But timing still grew roughly $O(n^4)$ empirically
  across $n=10,15,21,30,40,50$ (0.05s → 93.5s) — traced to the prototype
  recomputing the *entire* active-set linear system from scratch every minor
  iteration ($O(r^3)$ per solve) rather than incrementally updating a
  factorization as the active set changes by one element at a time (a
  standard technique in the Wolfe-algorithm implementation literature, not
  exotic — would bring this down to roughly $O(n^3)$ or better). Checked
  whether this was instead exact-arithmetic coefficient blowup (a classical
  risk with exact linear algebra) — it wasn't: denominators at $K_{30}$ stay
  exactly at `30`, matching theory, no growth beyond that.
- **"Integer instead of rational" falls out for free**, no separate algorithm
  needed: since the denominator is guaranteed to divide $|C|$, clearing
  denominators on the exact result directly gives an integer packing. On
  house: weights $1/3,1/3,1/3$ scaled by $|C|=6$ give multiplicities $2,2,2$
  — exactly the "6 spanning trees, each edge in 4" framing from your packing
  observation above, read directly off the rational solution, no separate
  integer-specific algorithm required.

> **Checked and rejected: do *not* replace the C++ solver's Cunningham engine
> with a unified whole-graph Wolfe solver.** Tempting since Wolfe's algorithm
> produces the pmf as it goes (no separate elaborator reconstruction) — but
> tested head-to-head on `examples/nested` (60 vertices, 310 edges):
> Cunningham (existing C++) takes 0.291s; Wolfe's algorithm run cold on the
> whole graph (exact arithmetic, no pre-decomposition) was still climbing
> past 127s at iteration 70 with no end in sight, active-set size still
> growing. Not just a language gap (Python vs. C++) — the growth pattern
> (active set ~ linear in iteration count, cost ~ cubic per iteration) matches
> the same scaling problem seen on $K_n$ above, and reflects a real
> complexity-theoretic gap: Wolfe's algorithm's worst-case bounds for general
> submodular minimization are historically much weaker than the
> strongly-polynomial, matroid-specific max-flow algorithm Cunningham's
> approach already uses. Applying Wolfe's algorithm *only* to already-decomposed
> homogeneous pieces with a known target (as PR 2 already does — that's why
> house converges in a handful of iterations) is a fundamentally easier
> problem than discovering $\eta^*$ from scratch, which is why that division
> of labor is being kept rather than unified. If this direction is revisited,
> re-run this comparison first.

**A structural conjecture worth checking before either algorithm is finalized
— the packing-problem framing.** You noted that the house graph's problem is
equivalent to choosing 3 (or 6) spanning trees so each edge appears in exactly
2 (or 4) of them, and more generally, for a homogeneous graph with $n$
vertices and $m$ edges, choosing $m$ spanning trees (with repetition) so each
edge appears in exactly $n-1$ of them. That's exactly right, and it isn't
just a fractional/probabilistic statement — $\theta=(n-1)/m$ with denominator
literally $m=|C|$ means this is asking for an **integer** decomposition of
$(n-1)\cdot\mathbb 1_C$, not merely a fractional one. This connects to the
**integer decomposition property (IDP) of matroid base polytopes** — I
believe (via Edmonds' matroid union theorem) it's a classical, provable fact
that base polytopes of matroids have IDP, which would guarantee an *exact
integer* $m$-tree packing always exists here, not just as a happy accident on
house.
- [x] **Action item resolved empirically, not yet by citation.** Not
  confirmed against a reference (still worth doing, e.g. Schrijver,
  *Combinatorial Optimization: Polyhedra and Efficiency*, the matroid union
  chapter), but confirmed *computationally*: a constructive matroid-exchange
  packing algorithm (next bullet) found a genuine integer $m$-tree packing on
  the diamond graph (brute-force cross-checked) and, more importantly, on the
  real pathological case — the round-2 K20-shaped piece of `examples/nested`
  (`|C|=190`) where Wolfe's algorithm, column generation, and even a MILP
  solver all failed or gave non-integer results (see §5.1.5). So IDP holding
  here isn't just a house-graph happy accident.
- [x] **Constructive matroid-union-type algorithm: prototyped, works, but
  NOT used in production — see §5.1.5 for why.** Implemented as two-tier
  matroid exchange (single-hop swaps, falling back to BFS multi-hop
  augmenting chains) in `scratch/matroid_union_packing.py`. Validated on
  $K_n$ up to $K_{100}$ and multi-level "house" graphs up to level 3 — but
  found to be **seed-dependent and incomplete** at level 4 (2 of 5 random
  seeds got stuck with a small residual imbalance), meaning it isn't a
  reliably-correct algorithm on its own. Superseded by the deflation-based
  approach (§5.1.5), which sidesteps the completeness question entirely by
  construction rather than needing a provably-complete search. Kept as a
  validated reference implementation, not deleted, but not on the path to
  the certificate builder.

### 5.1.5 Medium gap, current architecture — deflation, then Wolfe's algorithm per piece

**This section supersedes §5.1's "PR 2 uses `min_norm_point_wolfe`
specifically" wherever the two disagree.** §5.1 above is kept for the
Wolfe-vs-AFW-vs-column-generation history (still accurate on its own terms),
but real multi-round validation (the open task §5.1 itself flagged) revealed
Wolfe's algorithm alone isn't sufficient, and this section is the fix that's
now actually implemented and tested.

**What broke, and why it's not a Wolfe's-algorithm bug.** Run cold on the
real round-2 piece of `examples/nested` (a K20-shaped shrunk multigraph,
`|C|=190`), Wolfe's algorithm doesn't converge — its active set keeps
growing without settling. The underlying cause: that graph is *homogeneous*
(no vertex-induced subgraph exceeds its own density — guaranteed by
Cunningham's algorithm's own correctness proof, the same fact §5.1 already
relied on for existence) but **not *strictly* homogeneous** — a proper
subgraph (a "core") *ties* the graph's own density exactly. When that
happens, some spanning trees genuinely cannot appear in any pmf hitting a
uniform marginal ("forbidden trees" — a real, unavoidable feature of the
target polytope, not a solver artifact), and Wolfe's algorithm, built for
the strictly-homogeneous case, has no clean way to detect or terminate
around this — it just doesn't converge.

**The fix: guarantee Wolfe's algorithm never sees a non-strictly-homogeneous
graph, instead of trying to detect when it's struggling.** A homogeneous
graph that isn't strictly homogeneous has a *unique minimal* tied proper
subgraph (its "core"); once contracted to a point, the graph left behind is
either strictly homogeneous (done) or has a smaller core one level down
(recurse). This is a real theorem (Albin, Lind, Melikyan, Poggi-Corradini,
"Minimizing the Determinant of the Graph Laplacian," *Journal of Graph
Theory*, 2025, Theorem 8.1), not a heuristic. So: **always deflate first**
(peel off cores via `core_deflation.deflation_sequence` until only a rigid,
strictly-homogeneous base remains), *then* run `min_norm_point_wolfe`
independently on each resulting piece. This was specifically the resolution
to a design question raised mid-session: "isn't detecting Wolfe's algorithm
failing hard?" — yes, and deflating first sidesteps needing to detect
anything, since every piece handed to Wolfe's algorithm is guaranteed safe
by construction.

**Core detection: exact-integer max-flow, not continuous optimization.**
The paper above also gives a continuous (minimum-determinant optimization)
characterization of the core, and it was tried first — it correctly
identifies cores, but the "has this converged or is it still diverging"
check (comparing floating-point solves at two tolerances) turned out
unreliable in practice; the exact analytic gradient available for that
objective converges too precisely for the heuristic to distinguish the two
cases. `core_deflation.find_core` instead uses an exact-integer max-flow
construction (Goldberg's densest-subgraph method, adapted from the classical
$|E(S)|/|S|$ density to this project's $|E(S)|/(|V(S)|-1)$ one). Three real
traps surfaced building it, all handled in the implementation (see the
module's own docstring for the full detail, kept in sync with the code —
don't duplicate the explanation here):
1. An unconstrained min cut degenerates to the empty set under the `-1`
   density; fixed by anchoring on an edge (forcing both endpoints
   source-side) rather than a single vertex, since single vertices
   *vacuously* tie under this density and don't fix the degeneracy.
2. `networkx.minimum_cut`'s returned side is the *maximal* min-cut
   minimizer, not the minimal one needed to find a genuine smaller core —
   its source computes reachability *to* the sink, not *from* the source.
   The minimal side has to be computed by hand from a properly-conserved
   max flow's residual graph.
3. Nested ties are real (e.g. stacking self-similar graph "stories" so every
   top-down suffix ties the same density) — recursing into whatever tied
   set is found first (not the whole edge list) correctly converges to the
   true minimal core, but is edge-order sensitive enough to be roughly
   cubic in an adversarial construction. Real solver-dispatched graphs
   aren't expected to nest this deeply; **not yet validated against a real
   deeply-nested shrunk graph**, only synthetic worst-case towers — flagged
   as an open item below.

**Implementation, tested:**
- `python/src/discrete_modulus/core_deflation.py` — `find_core` (returns a
  core's vertex set, or `None` if strictly homogeneous),
  `deflation_sequence` (repeatedly finds and contracts). Multigraph-safe
  (parallel-edge capacity correctly accumulated in the max-flow network —
  a real bug caught and fixed while building this, since real shrunk graphs
  from repeated contraction generally have parallel edges).
  `python/tests/test_core_deflation.py` (13 tests): strictly-homogeneous
  graphs report no core; `demo.house_graph()`'s core is exactly its chord
  triangle (matches independent brute-force/determinant-argument checks
  from earlier exploration); nested ties on a multi-level house-graph family
  peel exactly one story per level, not a larger nested union; multigraph
  regression tests for the capacity-accumulation fix.
- `python/src/discrete_modulus/pmf_construction.py` — `build_factored_pmf`:
  deflates, then runs `min_norm_point_wolfe` on each piece via
  `MinimumSpanningTree` (see below), returning a `FactoredPmf` (independent
  per-piece local pmfs + edge provenance back to the original graph, exact
  `.marginal()`, Monte-Carlo `.sample()` for validation).
  `python/tests/test_pmf_construction.py` (7 tests): exact uniform marginals
  on house graph, multi-level house graphs (parametrized), a strictly-
  homogeneous baseline case, and a genuine multigraph input; sampled trees
  independently checked as genuine spanning trees.
- `python/src/discrete_modulus/families/networkx_families.py`'s
  `MinimumSpanningTree` — **fixed to support `nx.MultiGraph`** (a real bug:
  `G[u][v]["enum"] = i` silently corrupted `MultiGraph` inputs, since
  `G[u][v]` there is a dict of parallel edges, not one edge's attribute
  dict). Needed because both a round's own shrunk multigraph and a
  deflation piece are generally multigraphs.

**Why the certificate's shape has to change, and how it maps to Lean.** The
factored representation (independent per-piece local pmfs, not a flat tree
list) is a deliberate design choice, not just an implementation detail of
the Python builder — see the discussion that produced it:
- **Never relabel vertices or edges.** Rather than the builder's internal
  contraction (which invents synthetic vertex names like `__core_3__` at
  each level, fine for computation but opaque for a certificate a Lean
  proof has to parse), the certificate should describe each deflation level
  as a **partition of the original graph's own vertices into equivalence
  classes** ("these original vertices are currently identified together"),
  with every edge referenced by its original endpoints throughout. This
  generalizes cleanly to the multi-*round* structure the solver already has
  (a round's own shrunk multigraph is itself a quotient by earlier rounds'
  `crit_set`s — the same kind of laminar nesting one level up), so the whole
  multi-round, multi-core computation is describable as *one* laminar family
  over the original vertex set, not two different mechanisms.
- **The underlying fact justifying "gluing independently-chosen local trees
  gives a genuine spanning tree" is a general matroid fact, not
  graph-specific, and it's already in Mathlib.** For any matroid $M$ and any
  subset $A$ of the ground set: a basis of the restriction $M|_A$ union a
  basis of the contraction $M/A$ is a basis of $M$ — no closedness/flat
  condition on $A$ needed (though the vertex-induced edge sets this project
  uses always happen to be flats, for what it's worth). Mathlib's
  `Mathlib.Combinatorics.Matroid.Minor.{Contract,Restrict}` already has this
  (`Indep.union_isBasis_union_of_contract_isBasis`), proved for *any*
  matroid — confirmed directly usable against `graphicMatroid` in the Lean
  spike (§4 Phase B). This means the Lean verifier's per-piece checks stay
  small (bounded by that piece's own edge count) regardless of how deep the
  nesting goes or how large the flat product *would* be if materialized —
  the exponential blowup the factored representation avoids in Python never
  has to be reasoned about in Lean either.
- **Expected usage ($\eta$) also decomposes cleanly**, for the same
  independence reason: since pieces are edge-disjoint and chosen
  independently, $\eta_e$ for an edge owned by piece $P$ is exactly $P$'s
  own local marginal at $e$ — no cross-piece interaction to reason about,
  in Python (`FactoredPmf.marginal()`, implemented) or in Lean (not yet
  formalized, but expected to follow from linearity of expectation over
  independent pieces — worth checking Mathlib's `PMF` type, which has
  product/independence tooling that might make this *easier* to formalize
  than a flat list, not harder).
- **Not yet resolved:** the actual on-disk/JSON certificate schema for this
  laminar-family representation (§6 still only has the old flat-list
  sketch), and the exact Lean-side type for "this piece's own local
  quotient" (some vertex-block partition, likely a `Quotient`/`Setoid` over
  the block — standard Lean pattern, doesn't reintroduce synthetic vertex
  names into anything the certificate itself claims, but hasn't been
  designed in detail yet).

**Open items specific to this section (not yet done):**
- [ ] Certificate schema for the laminar-family/vertex-block representation
  (§6 needs a real rewrite, not just the old flat sketch marked stale).
- [ ] Gluing pmfs *across* rounds (not just within one round's deflation),
  using the same laminar-nesting idea applied to the solver trace's own
  round structure.
- [ ] Validate `core_deflation`/`pmf_construction` against a *real* solver
  trace end to end (only synthetic graphs tested so far: house, multi-level
  house towers, $K_n$, one synthetic multigraph).
- [ ] Formalize the $\eta$-decomposition-via-independence argument in Lean
  (informally justified above, not yet attempted) — check Mathlib's `PMF`
  type first before hand-rolling anything.
- [ ] Design the Lean-side "local quotient" vertex type (a block's immediate
  children, some vertices still-unmerged originals, others nested
  sub-blocks) — sketched as a `Quotient`/`Setoid` above, not designed in
  detail.

### 5.2 Biggest gap — admissibility of ρ

Given PR 4's definitional lemma (admissible ⟺ MST weight $\ge 1$), the
Kruskal-oracle shortcut isn't an approximation of admissibility — it computes
*exactly* the right quantity, just via an implementation that isn't proven
correct yet. That reframing is worth keeping front-of-mind: the v1 gap is
narrowly "we trust this specific MST implementation," not "we've approximated
what admissibility means."

v1 plan (per your answer): implement Kruskal in Lean as a plain computable
function, no correctness proof, and treat "Kruskal's returned weight $\ge 1$"
as the operational definition of admissibility for certificate-checking
purposes. Document this prominently (§3, §4's PR 5 checklist) rather than
letting it sit quietly as an implementation detail. PR 6 is the tracked
follow-up to prove Kruskal correct and remove the gap — scoped so it never
blocks Phases A-C.

## 6. Certificate format

**History: two earlier sketches, both superseded, kept below only for the
record.** v1 (a flat `"trees"` list) predates the deflation-based design
(§5.1.5) and doesn't fit it — it would require materializing the full
Cartesian product across every deflation level, exponential in nesting
depth. v2 (a `"blocks"`/`"parent"` tree) was the right shape *category*
(factored, laminar) but wrong in its specifics — it assumed the laminar
family needed general tree/parent-pointer structure. §4's gluing work
(`Pmf.glue`, `isBase_contract_iff_of_isBasis_restrict`) found that it
doesn't: read against the actual builder (`pmf_construction.py`) and
solver trace (`solver_trace.hpp`) rather than re-derived from prose, both
the within-round core-deflation nesting and the across-round `crit_set`
nesting reduce to *one flat, ordered list* — verified by a single
left-fold of `Pmf.glue`, not a general tree walk. v3 below reflects that.

```jsonc
{
  "certificate_version": 3,
  "graph": { "vertices": [...], "edges": [[u, v], ...] },
  // A flat, ORDERED list of pieces -- one per within-round deflation core,
  // or per solver round if it needed no further deflation. Order matters:
  // it must match discovery order (round 1's pieces, in their own
  // discovery order, then round 2's, ...), the same order
  // `FactoredPmf.pieces`/`SolverTrace.rounds` already produce. The
  // verifier processes this list via one left-fold of `Pmf.glue`: at step
  // i, "everything folded in so far" (steps 1..i-1) plays `Pmf.glue`'s
  // `μA` argument, and piece i's own `local_pmf` plays `μRest` --
  // provable-compatible with whichever tree of the earlier pieces was
  // drawn, automatically, no certificate-side bookkeeping needed for that
  // part (§4's `isBase_contract_iff_of_isBasis_restrict`).
  "pieces": [
    {
      // This piece's own edge scope, as indices into the TOP-LEVEL
      // "edges" array above (never relabeled/local indices -- see the
      // note below on why). Must be disjoint from every earlier piece's
      // "edges", and the union of all pieces' "edges" must be the whole
      // top-level "edges" list (checked by the verifier; see open items).
      "edges": [0, 2, 5],
      "local_pmf": {
        // Spanning trees of this piece, as edge-index lists into THIS
        // piece's own "edges" above (equivalently, into the top-level
        // "edges" array, since piece edges are a subset) -- global
        // indices throughout, per the note below.
        "trees": [{ "edges": [0, 2], "weight": [1, 2] }, ...]  // [num, den]
      }
    },
    ...
  ],
  "eta": [{ "edge": 0, "value": [1, 3] }, ...],
  "rho": [{ "edge": 0, "value": [1, 3] }, ...]
}
```

**Why tree edges are global (top-level) indices, not piece-local ones.**
Python's own `LocalPiece.provenance` maps *local* edge indices (dense,
`0..piece_size-1`, what `min_norm_point_wolfe`'s arrays actually use) back
to the original graph — but that's an implementation detail of running
Wolfe's algorithm efficiently, not something the certificate needs to
inherit. Using global indices everywhere means the verifier never needs a
local→global translation step at all: `Multigraph.IsForest`/`endpoints`
apply directly to a piece's declared trees exactly as they would to the
whole graph, matching §5.1.5's "never relabel vertices or edges"
principle already adopted for the same reason. The certificate builder
does the (cheap, untrusted) translation from Wolfe's local indices once,
at emission time.

**`local_pmf`'s shape was confirmed, not just sketched, by PR 4.**
`DiscreteModulusCert.Pmf` is literally "a `Finset` of edge sets plus a
rational weight each" — exactly the shape above — so `local_pmf.trees`
parses directly into a `Pmf`, no intermediate representation needed.
Weights parse as plain `ℚ` (`[num, den]`), never `ℝ≥0`/`NNReal` — see §4's
PR 4 entry for why `lean-modulus`'s own `ℝ≥0`-valued density vocabulary
turned out not to be reusable here at all.

**Open items — what PR 5's parser/verifier still needs to nail down and
check:**
- [x] **Fold driver — done.** `DiscreteModulusCert.PieceList`/
      `PieceList.glueAll` (`lean/DiscreteModulusCert/Glue.lean`) is exactly
      this section's `pieces` array, formalized: an inductive flat list
      where each block's pmf is typed relative to everything before it
      already contracted away, folded via a generalized `Pmf.glue`
      (generalized from a single fixed ambient `G.graphicMatroid` to an
      arbitrary ambient matroid — necessary because folding a *list* glues
      against growing intermediate restrictions `G.graphicMatroid ↾ X`,
      not just the top-level matroid). No `sorry` (axiom-checked).
- [x] **Partition-completeness check — resolved, at the type level rather
      than as a runtime check.** `PieceList.glueAllGraph` only accepts a
      `PieceList N Set.univ` (blocks' edges summing to literally
      `Set.univ`, matched by the *type* `PieceList N U`'s own index `U`)
      and produces `Pmf N` directly, ready for `certificate_optimality`.
      A verifier can only construct a `PieceList N Set.univ` if the
      certificate's pieces really do union to everything — the type system
      enforces the check rather than needing a separate runtime assertion.
- [ ] **Per-piece `IsBase` checking — still open, the main remaining PR 5
      gap.** `PieceList`/`Pmf.glue` assume each block's `Pmf` already has
      a proof `isBase : ∀ T ∈ support, M.IsBase T` — turning a
      certificate's raw `{edges: [...], weight: [...]}` JSON into that
      proof (a forest check — `Multigraph.IsForest`: no loops, injective
      endpoints, acyclic — plus a cardinality/spanning check against that
      block's own rank) isn't implemented or even sketched as Lean code.
      This is the one piece standing between "the fold driver exists" and
      "a real certificate can be parsed and checked" — genuinely the next
      thing to build. `hdisj` (`Pmf.glue`'s one remaining *pmf-level*
      hypothesis — a piece's trees never touch an earlier piece's edges)
      is a special case and is directly, cheaply decidable from the
      concrete edge-index lists once trees are constructed.
- [ ] **`vertices` is informational only, not load-bearing for
      verification** — every check above runs purely on edge sets
      (`Pmf.glue`, `IsForest`, etc. never mention vertices). Worth keeping
      in the schema for traceability back to `solver_trace.hpp`'s own
      per-round `vertices` field and for human debugging, but the
      verifier's correctness doesn't depend on it. Flagging explicitly so
      a future contributor doesn't assume it needs cross-checking against
      anything.
- [ ] Keep `certificate_version` independent from the PR 1 solver-trace
      version — they change on different schedules.

## 7. Definition of done / success criteria

- [ ] `examples/house` and `examples/nested` go end-to-end: solver (traced) →
      builder (certificate) → Lean verifier accepts, with the TCB caveat
      (§3) visible in the verifier's output.
- [ ] TCB ledger (§3) stays current and is linked from the top-level repo
      README once this work lands, not just this scratch doc.
- [ ] PR 6 tracked as follow-up work, not required for "v1 done."

## 8. Open questions (not yet resolved — flag before Phase C starts)

- Certificate size/scaling: no target graph size has been chosen yet for
  "how big can we certify" — worth picking one (e.g. `examples/nested`, or
  a small synthetic case) as the explicit target for v1 rather than
  discovering the practical ceiling during PR 5.
- Whether to check $\eta$-reconstruction fully in-kernel or trust the
  builder's $\eta$ and only re-derive it from $\mu$ (PR 5 checklist) —
  affects Lean proof/runtime cost; decide once PR 2's real output sizes are
  known.
- Definitional adequacy of the reused `lean-modulus` types (§2's reuse
  table, §3's TCB ledger): a short explicit sanity pass confirming
  `Multigraph`/`IsSpanningTree`/`Density`/`Adm` mean what this project needs
  them to mean, before PR 4 builds on top of them — cheap now, expensive to
  discover wrong after PR 5 is built. Partially covered for
  `IsSpanningTree` by the spike's `isSpanningTree_iff_isBase` (§4 Phase B,
  §5.1.5) but not `Density`/`Adm`.
- **Resolved (was: "New, from §5.1.5"), see §6:** the certificate schema is
  now designed (v3, a flat ordered `pieces` list) and grounded in both the
  actual Python builder's data shapes and a Lean-side proof of why the
  flat-list structure suffices (§4's PR 4 entry). Not fully closed though
  — §6 itself lists three concrete remaining open items (partition-
  completeness checking, per-piece `IsBase` checking, the fold driver)
  that are real PR 5 implementation work, not design gaps.
- **New, from §5.1.5:** whether `core_deflation`'s cubic-in-adversarial-cases
  performance is actually fine on real solver-dispatched graphs, or whether
  it needs the "principal partition of a matroid" style single-shot
  algorithm that was identified as a theoretically cleaner alternative but
  not implemented (only validated against synthetic worst-case towers, which
  real shrunk multigraphs are not expected to resemble — but this is an
  assumption, not yet checked against real data).
- **Resolved (was: "New, from §5.1.5"):** gluing pmfs *across* solver
  rounds, not just within one round's own deflation, turned out to need
  *no* additional treatment beyond within-round gluing — investigating
  `solver_trace.hpp` (§4's PR 4 entry) found rounds and deflation cores are
  structurally identical from the gluing machinery's point of view (both
  are just "some disjoint edge set with its own local pmf"), so the same
  flat-list fold (§6) covers both uniformly.

### Resolved since first written (kept for the record, not because they're
still open)

- ~~`lean-modulus` dependency mechanics: confirm the Lean toolchain and
  Mathlib revision `discrete-modulus/lean/` needs actually align with
  whatever `lean-modulus` is pinned to~~ — **confirmed working**, §4 Phase B.
- ~~Whether Wolfe's algorithm alone is sufficient for PR 2, pending real
  multi-round validation~~ — **no, it isn't; resolved via deflation**, §5.1.5.
