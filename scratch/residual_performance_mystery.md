Investigate and fix a residual performance mystery in lean/DiscreteModulusCert/ForestDecide.lean,
left over from a completed fix for a previously-exponential Reachable-decidability blowup.

## Background (already done, don't redo this)

`ForestDecide.lean`'s `instDecidableIsForestOfList` (a `Decidable (Multigraph.IsForest {e | e ∈ l})`
instance) used to hang on `cpp/examples/nested.certificate.json`'s 190-edge/20-vertex piece because
Mathlib's `SimpleGraph.Reachable` decidability instance is genuinely exponential (enumerates every
walk, no pruning). This was fixed in two layers, both already implemented and merged:

1. `FastReachable` section: a `Finset`-based BFS closure (`bfsStep`/`bfsClosure`) with fixed-point
   early termination, replacing the exponential Mathlib instance. Proven correct via
   `SimpleGraph.reachable_le_of_adj_le`.
2. `Components` section: a connected-components cache (`forestComponents`, `edgeVerts`,
   `decidableIsForestInsertOfComponents`) built once per base forest and queried cheaply per
   candidate insertion, wired into `CertChecker.lean`'s `checkTree` (previously each candidate
   re-ran a fresh reachability search against an unchanging graph).

Both are formally verified (no `Classical.choice`/`sorry` in the decision path), and
`lake exe verify_cert` now reports ACCEPTED for all three test certificates:
- `house.certificate.json`: ~2s
- `branch_test.certificate.json`: ~2.3s
- `nested.certificate.json`: ~42s (was: never completes)

`branch_test`'s `#eval` in `CertCheckerTest.lean` is re-enabled and fast. `nested`'s stays commented
out — not an algorithmic issue, but because Lean's *interpreter* (what `#eval` runs under) has
enough per-op constant-factor overhead that it pushes well past a smoke-test budget; `nested` is
verified via the compiled `verify_cert` executable instead.

## The open question

`nested`'s 42s is dramatically better than "never," but still far from the ~2s `branch_test` gets,
despite `decidableIsForestInsertOfComponents`'s per-candidate work theoretically being an O(1)-ish
`List`/`Finset` lookup against a precomputed components cache. Direct measurement (via a scratch
`lean_exe` bench harness, since regions the whole thing) isolated where the cost actually is:

- The *bare* connectivity check alone (`∃ c ∈ comps, edgeVerts (G.endpoints e) ⊆ c`, computed and
  forced directly) is genuinely fast: 60 candidates in ~0ms, compiled.
- Wrapping that same check inside `decidableIsForestInsertOfComponents` (which builds
  `isTrue (proof)` / `isFalse (proof)` values, where `proof` extracts named vertices via
  `obtain ⟨u, v, huv⟩ := Sym2.exists.mp ⟨G.endpoints a, rfl⟩` and then applies
  `isForest_insert_iff`) costs ~39ms/candidate — ~2.3s for 60 candidates.
- The *original*, pre-existing `decidableIsForestInsertOfList` (same proof-wrapping pattern, no
  components cache, just a fresh `bfsClosure` per call) shows the *same kind* of overhead
  (~65ms/candidate) — so this is NOT something the components-cache change introduced. It's an
  existing characteristic of the "isTrue/isFalse wrapping a Sym2.exists.mp-derived proof" pattern
  itself, present since `ForestDecide.lean` was first written.

**Important benchmarking gotcha, already hit once**: naively timing `let x := someComputation` with
`IO.monoMsNow` immediately before/after captures ~0ms even for expensive `x`, because Lean defers
the actual computation until `x` is *forced* (e.g. by a later `IO.println s!"...{x}..."` that
interpolates it). You MUST force the value (e.g. `IO.println s!"{x}"` or `x.all (·==...)`) *before*
capturing the "end" timestamp, or you'll measure ~0ms everywhere and the real cost will silently
show up as unattributed time in the enclosing scope. This cost me significant time to figure out —
don't repeat it.

## What's been ruled out

- `Sym2.exists`'s `.mp` direction is NOT `Classical.choice`-based — it's built from
  `Quotient.exists` (`Mathlib/Data/Quot.lean`), whose proof uses `Quotient.ind`
  (`q.ind (motive := (p · → _)) .intro hq`), which is a legitimate choice-free Prop-to-Prop
  eliminator. So "the witness extraction secretly needs Classical.choice at runtime" is not the
  explanation, at least not directly.
- An attempted fix — replacing `Sym2.exists.mp` with `Sym2.ind`/the `cases_eliminator`-tagged
  eliminator (`induction z with | _ u v => ...` after `generalize hz : G.endpoints a = z`) — was
  started but reverted incomplete due to time pressure; it was never actually benchmarked. This is
  the most promising untried lead.

## Suggested next steps

1. Properly redo the `Sym2.ind`-based rewrite of `decidableIsForestInsertOfComponents`'s proof
   bodies (both the `isFalse` branch around line ~628 and the `isTrue` branch around line ~639 in
   the current file — check current line numbers, this has likely shifted) and re-benchmark with
   proper forcing. If this resolves it, apply the same fix to `decidableIsForestInsertOfList`.
2. If that doesn't help, isolate further: temporarily replace the proof bodies with `sorry` (in a
   throwaway branch, never commit) to see if `isTrue (fun _ => sorry)` / `isFalse (fun _ => sorry)`
   is fast. If YES, the cost is in constructing/erasing the *specific* proof content (implicates
   `isForest_insert_iff` or `connected_forestComponents_iff` specifically, not proof-wrapping in
   general). If NO (still slow even with `sorry`), the cost is something about the `Decidable`/
   `dite`-chain construction itself, independent of proof content — investigate whether it's a
   proof-erasure failure in Lean 4's compiler for this shape of term (e.g. try isolating with a
   minimal reproduction outside this codebase and consider filing a Lean4/Mathlib issue).
3. Rebuild the scratch bench harness pattern from this investigation if useful: a `lean_exe` target
   (add to `lakefile.toml`, remove when done) importing `DiscreteModulusCert.CertChecker`, reading
   `nested.certificate.json` directly, calling `checkPiece`/`decidableIsForestInsertOfComponents`
   in isolation with `IO.monoMsNow` brackets — remember the forcing gotcha above.
4. Target: get `nested`'s `lake exe verify_cert` time down from ~42s toward low single digits,
   ideally close to `branch_test`'s ~2.3s given both should have comparable per-candidate cost once
   this is fixed.

## Update (2026-07-24): root cause found via `perf`

Picked this up and made progress in two stages.

**Stage 1 — the `Sym2.ind` rewrite (the "most promising untried lead" above)
was tried and does help, modestly.** Replaced `obtain ⟨u, v, huv⟩ :=
Sym2.exists.mp ⟨G.endpoints a, rfl⟩` with `induction huv : G.endpoints a with
| _ u v =>` in both `decidableIsForestInsertOfList` and
`decidableIsForestInsertOfComponents` (both branches of each). This compiles
cleanly and is a strict improvement, but it's not the dominant cost:
`nested`'s `lake exe verify_cert` went from ~32s (this machine's baseline,
not directly comparable to the ~42s figure above) to a consistent ~25.7s
across repeated runs. Applied and kept — no reason not to.

**Stage 2 — the real bottleneck, found by installing `perf` (WSL2 needs the
kernel-generic package's binary invoked directly, e.g.
`/usr/lib/linux-tools-6.8.0-136/perf`, since the `/usr/bin/perf` wrapper
refuses to run against WSL2's non-standard kernel version string) and
profiling `lake exe verify_cert` on `nested` directly.**

`perf report` puts 57% of total cycles in `List.elem` (`l_List_elem___redArg`),
reached via `instBEqOfDecidableEq` → `Sym2.instDecidableRel`, called from
**`instDecidableRelAdjToSimpleGraphOfList`** — the adjacency-decidability
instance this file's own docstring already flags as "scans the edge list."
That instance is called from **`bfsStep`**'s `Finset.univ.filter (H.Adj u)`
line — and `Finset.univ : Finset V` there is **the whole graph's vertex
set**, not just the vertices touched by the edge list `l` currently being
closed over.

This matters because `nested.certificate.json`'s graph has **60 vertices
total across all 3 pieces**, but any single piece/tree only uses ~20 of
them. `bfsClosure`'s termination argument (`FastReachable` section) bounds
the number of rounds by `Fintype.card V` — i.e. 60, not the ~20 actually
relevant to a given `checkTree` call — and every one of those rounds scans
all 60 vertices via `Finset.univ`, each vertex's adjacency check doing a
linear scan through `l` (up to 190 edges) with `Sym2`-equality comparisons
that carry real allocation/refcounting overhead (visible in the profile as
`mi_free` / `lean_dec_ref_cold` under the same call path). `forestComponents`
(which wraps `bfsClosure`) runs once per `checkTree` call, and there are 16
such calls across `nested`'s pieces — so this cost is paid 16 times over.

**Why every manual isolation attempt before `perf` came back "fast" (a
real trap, worth recording for next time):** stubbing out
`decidableIsForestInsertOfComponents`'s `hreach` branch (or its whole body)
with `sorry` didn't just remove the per-candidate check — since `comps`
(built via `forestComponents`, the *actual* expensive call) became
provably unused once `hreach` no longer referenced it, the compiler's dead-
argument elimination silently dropped the `forestComponents` computation
at the `checkTree` call site too. Every hand-built reproduction (matching
vertex/edge counts, using the real functions directly, runtime- vs.
compile-time-known sizes) missed this because none of them preserved a
call to `forestComponents` whose *result* was actually forced downstream
in a way matching the real `checkTree`/`extra.all` shape closely enough.
Lesson: when isolating a suspected hot function, checking that the
isolated version still forces every value the real call site forces is at
least as important as matching data shapes/sizes — a much sharper trap
than the "let-binding not forced" gotcha already documented above, since
here the *compiler*, not just laziness, was quietly doing the eliding.

**Untried but well-scoped fix:** restrict `bfsStep`'s frontier expansion to
a precomputed vertex-support set for `l` (e.g. the union of `edgeVerts
(G.endpoints e)` over `e ∈ l`) instead of `Finset.univ : Finset V`. BFS
starting from vertices only reachable via `l`'s own edges can never leave
that support set, so this should be sound, but it requires re-deriving
`subset_bfsStep`/`bfsClosure`'s termination argument (currently keyed to
`Fintype.card V`) against the smaller support set's cardinality instead,
plus re-checking `connected_forestComponents_iff` and everything downstream
still goes through cleanly. Not attempted yet — a genuine proof-engineering
task, not a quick patch, and the right next step if `nested`'s ~25s is
still worth chasing further.

## Constraints (must hold throughout)

- No `Classical.choice`/`sorry` in the final decision path — must stay genuinely computable.
- Must keep working both as compiled/interpreted runtime code (`CertChecker.lean` calls it on data
  parsed at program runtime) and under `native_decide` for `HouseCert.lean`/`IsBaseCheck.lean`'s
  compile-time literal proofs.
- After any fix, rebuild and re-run `lake exe verify_cert` against all three certificates in
  `cpp/examples/`, and rebuild `DiscreteModulusCert.HouseCert`/`ForestDecideTest`/`IsBaseCheck` to
  confirm no regressions.
