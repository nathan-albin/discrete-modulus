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

## Constraints (must hold throughout)

- No `Classical.choice`/`sorry` in the final decision path — must stay genuinely computable.
- Must keep working both as compiled/interpreted runtime code (`CertChecker.lean` calls it on data
  parsed at program runtime) and under `native_decide` for `HouseCert.lean`/`IsBaseCheck.lean`'s
  compile-time literal proofs.
- After any fix, rebuild and re-run `lake exe verify_cert` against all three certificates in
  `cpp/examples/`, and rebuild `DiscreteModulusCert.HouseCert`/`ForestDecideTest`/`IsBaseCheck` to
  confirm no regressions.
