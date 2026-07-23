# Reading plan: `spanning-tree-cert` branch code review

Every file this branch adds or changes, outside `scratch/` (which will
eventually be removed and isn't part of the review). Organized into tiers
with a suggested reading order within each; check boxes off as you go.

**Total**: ~48 files, roughly 5,900 lines in the files with real content
(Tiers 1–3), dominated by two Lean files (`Soundness.lean`,
`ForestDecide.lean` — together over half the Lean line count). If you
want to split this across sessions, Tier 0 + Tier 1 + Tier 2 is a natural
first sitting, and Tier 3 alone is a second (possibly split again around
`Soundness.lean`).

**Since this plan was written**: `HouseCert.lean` (706 lines) was removed
-- it was the first full hand-transcribed run of the whole verification
chain on the house example, superseded by `EndToEndTest.lean` once a real
JSON parser and the generic `Soundness.lean` theorems existed. Its one
genuinely distinct result (house's uniform `rho` needing no Kruskal axiom)
was extracted first, into `Admissibility.lean`'s
`isAdmissible_const_div_ncard_of_isBase` -- a ~15-line addition, noted in
its Tier 3 entry below.

## Tier 0 — Orientation (read first, ~20 min)

These are the `docs/certification/` files — read them before anything
else; they'll make every file below faster to place.

- [ ] `docs/certification/README.md` — architecture overview, the
      three-stage pipeline, trust-per-stage table.
- [ ] `docs/certification/walkthrough.md` — the house graph through all
      three stages with real file contents at each step.
- [ ] `docs/certification/pipeline.md` — the "how," per stage, naming
      actual files/functions. This one doubles as a map for Tier 3 below.
- [ ] `docs/certification/schema.md` — field-by-field reference for both
      JSON formats.
- [ ] `docs/certification/trust.md` — the TCB ledger; read this
      critically, since it's the whole point of the exercise.

## Tier 1 — C++ solver changes (small, ~10 min)

- [ ] `cpp/include/discrete_modulus/graphs.hpp` (+39 lines) — adds
      `is_simple_graph`, a template predicate checking no self-loops/
      parallel edges.
- [ ] `cpp/include/discrete_modulus/cunningham.hpp` (+5 lines) —
      `spanning_tree_modulus` now asserts `is_simple_graph(g)` on entry.
      Worth checking: does this assert fire correctly, and is the
      reasoning in the assert message (silently-wrong `edge(u,v,g)`
      lookups on a multigraph) actually right?
- [ ] `cpp/test/test_graphs.cpp` (+23 lines) — three new `TEST_CASE`s for
      `is_simple_graph` (accepts every demo graph, rejects a self-loop,
      rejects parallel edges regardless of endpoint order).

## Tier 2 — Python: the certificate builder (~1–1.5 hr)

Suggested order — foundational types first, then the pieces that build
on them:

- [ ] `python/src/discrete_modulus/protocols.py` (+70 lines) — new home
      for `SupportEntry`/`MinNormPointResult` (moved out of
      `min_norm_point.py` so `pmf_construction.py`/`tree_packing.py`
      don't have to import it). Quick file; check the move didn't lose
      anything.
- [ ] `python/src/discrete_modulus/min_norm_point.py` (−69 net lines,
      mostly the moved-out types) — Wolfe's algorithm + AFW, no longer on
      the production path (superseded by tree packing below) but kept
      for its own test suite and comparison value. Mostly unchanged
      logic; the diff is really just the import.
- [ ] `python/src/discrete_modulus/tree_packing.py` (346 lines, new) —
      the actual per-piece pmf solver now in production: constructive
      integer spanning-tree packing (away-step swaps + a BFS
      matroid-exchange fallback). This replaced Wolfe's algorithm because
      of a real, previously-observed unpredictable convergence tail —
      worth understanding the two-tier algorithm itself, since it's the
      one piece of nontrivial new math logic in the Python side.
- [ ] `python/src/discrete_modulus/pmf_construction.py` (+46/−changed
      lines) — `_solve_piece` now calls `build_tree_packing` instead of
      `min_norm_point_wolfe`; check the `theta = (n-1)/m` computation and
      the `RuntimeError` fallback if packing doesn't converge.
- [ ] `python/src/discrete_modulus/certificate_builder.py` (394 lines,
      new) — the actual builder: solver trace → shrunk multigraph per
      round → `build_factored_pmf` → global edge-index translation →
      **reversed round order** in `pieces` (read `build_certificate`'s
      docstring carefully here — this is the one place a subtle ordering
      bug was actually caught and fixed) → `eta`/`rho` computation →
      `validate_certificate`. This is the file most worth reading
      line-by-line.
- [ ] `python/tests/test_certificate_builder.py` (104 lines, new) —
      end-to-end tests against real `house`/`nested` traces, including a
      JSON-Schema validation pass against
      `docs/certification/certificate_schema.json`.
- [ ] `python/src/discrete_modulus/__init__.py` (+28/−changed) — just the
      module-listing docstring, updated to mention
      `certificate_builder`/`tree_packing` and stop describing the now-
      superseded Wolfe-based architecture.

## Tier 3 — Lean verifier (the bulk of the review, ~3–4+ hr)

Ordered bottom-up by dependency — each file mostly only needs the ones
above it.

- [ ] `lean/DiscreteModulusCert/Basic.lean` (16 lines) — smoke test:
      confirms the pinned `lean-modulus` commit exposes the two bridging
      lemmas (`isSpanningTree_iff_isBase`,
      `isBase_union_of_isBase_restrict_isBase_contract`) everything else
      builds on.
- [ ] `lean/DiscreteModulusCert/Family.lean` (152 lines) — the
      `ℚ`-native vocabulary: `CertDensity`, `pairing`, `sqNorm`,
      `IsAdmissible`, `Pmf` (a `Finset` of edge-sets + weights).
      Deliberately *not* reusing `lean-modulus`'s own `ℝ≥0`-valued
      `Density`/`Adm` — worth checking the stated reason (no subtraction
      in `ℝ≥0`, needed for Cauchy-Schwarz) actually holds up.
- [ ] `lean/DiscreteModulusCert/Optimality.lean` (120 lines) —
      `certificate_optimality`: the Cauchy-Schwarz duality argument
      itself. Probably the single most important proof in the project to
      check carefully — everything downstream just wires data into this.
- [ ] `lean/DiscreteModulusCert/Glue.lean` (440 lines) — `Pmf.glue`
      (combining two pmfs across a matroid restrict/contract split) and
      `PieceList`/`glueAll` (folding a whole certificate's `pieces`
      list). Check `Pmf.glue_marginal`/`glueAll_marginal` especially —
      that's what lets `eta` be computed without ever materializing the
      exponential combined support.
- [ ] `lean/DiscreteModulusCert/IsBaseCheck.lean` (87 lines) —
      `isBase_contract_restrict_iff_isForest`, reducing "is this a
      genuine base of the piece's matroid" to "is this edge set a forest
      of the original graph."
- [ ] `lean/DiscreteModulusCert/ForestDecide.lean` (659 lines, the
      second-largest file) — makes `Multigraph.IsForest` genuinely
      `Decidable` via structural recursion, since Mathlib's natural route
      doesn't synthesize. Dense; the module docstring explains the two
      real Lean subtleties it ran into (large elimination on
      `Sym2.exists`, well-founded recursion not reducing under `decide`)
      — worth following those closely since they're exactly the kind of
      thing a reviewer might otherwise assume was arbitrary.
- [ ] `lean/DiscreteModulusCert/ForestDecideTest.lean` (55 lines) —
      smoke test on a hand-built 3-cycle; also explains why
      `native_decide` is needed here instead of `decide`.
- [ ] `lean/DiscreteModulusCert/Kruskal.lean` (68 lines) — the greedy
      MST algorithm itself. **This is the one piece of the whole
      pipeline that's deliberately unverified** — read it as "is this a
      faithful, if unproven, implementation of Kruskal's algorithm," not
      as a proof to check.
- [ ] `lean/DiscreteModulusCert/KruskalTest.lean` (46 lines) —
      hand-checked triangle smoke test.
- [ ] `lean/DiscreteModulusCert/Admissibility.lean` (~95 lines) — the
      trust boundary made explicit: a named `axiom` bridging "Kruskal's
      computed weight ≥ 1" to `IsAdmissible`. Worth confirming this axiom
      states exactly what it should and nothing more. Also has the
      complementary fact `isAdmissible_const_div_ncard_of_isBase` (a
      uniform density is admissible directly from "every base has the
      same cardinality," no MST oracle needed) — extracted from the
      now-deleted `HouseCert.lean`, worth checking it's actually used
      somewhere (`EndToEndTest.lean` doesn't currently invoke it, since
      the generic path always goes through the Kruskal axiom regardless
      of whether `rho` is uniform — worth deciding if that's fine or
      worth wiring up).
- [ ] `lean/DiscreteModulusCert/CertChecker.lean` (318 lines) — the
      runnable JSON checker: `RawCertificate`/`RawPiece`/`RawTree`
      (parsed via `deriving FromJson`), `checkPiece`/`checkPieces`,
      `sumTreeContributions`, and `checkCertificate` itself. This is the
      executable surface that everything in `Soundness.lean` proves
      things *about* — good to read adjacent to it.
- [ ] `lean/DiscreteModulusCert/CertCheckerTest.lean` (49 lines) —
      `#eval`s against real `house`/`branch_test` certificate files
      (`nested`'s is deliberately commented out — interpreter too slow,
      see its docstring).
- [ ] `lean/DiscreteModulusCert/Soundness.lean` (1057 lines, the largest
      file) — the generic checker-to-proof-term theorem:
      `checkCertificate_sound` and the capstone `checkCertificate_optimal`.
      This is where "the checker said ok" gets turned into an actual
      kernel-checked proof. Budget real time for this one; it's dense
      fold-vs-sum bridging lemmas (`foldlM_getD_eq_of_forall` etc.)
      before it gets to the two headline theorems at the bottom —
      reading top-to-bottom in order is probably right here since each
      section is used by the next.
- [ ] `lean/DiscreteModulusCert/EndToEndTest.lean` (89 lines) — the
      strongest instance of the whole claim: `house`/`nested`'s real,
      on-disk certificate JSON, parsed by Lean's actual JSON parser at
      compile time (`include_str`), fed straight through
      `checkCertificate_optimal`. Short file, but worth checking the
      `Option.get`/`native_decide` unwrapping is actually sound (no
      silent fallback value).
- [ ] `lean/Main.lean` (44 lines) — the `verify_cert` CLI wrapping
      `checkCertificateJson`, plus the printed Kruskal caveat.
- [ ] `lean/DiscreteModulusCert.lean` (15 lines) — the umbrella import
      file. Worth a 10-second check that every file above is actually
      imported here — a past bug on this branch was new files silently
      never being built because they weren't wired into this file.

## Tier 4 — Generated example data (spot-check, ~15 min)

Not really "code" — these are checked-in outputs, worth spot-checking
against Tier 0/2's claims rather than reading line by line.

- [ ] `cpp/examples/house.trace.json`, `nested.trace.json`,
      `branch_test.trace.json` — do these match `solver_trace.hpp`'s
      format?
- [ ] `cpp/examples/house.certificate.json`, `nested.certificate.json`,
      `branch_test.certificate.json` — spot-check `eta`/`rho` against the
      corresponding `.eta` file (`house.eta` already existed; check
      `branch_test.edges`/`.eta` too, both new).
- [ ] `cpp/examples/branch_test.edges` — the new fixture: two $K_{10}$
      lobes joined by a 3-edge bridge, built specifically to exercise
      non-linear round dependencies.

## Tier 5 — Build/config plumbing (~15 min, mostly skim)

- [ ] `lean/lakefile.toml` — pins `lean-modulus` to a specific commit;
      confirm the commit hash is the one you expect.
- [ ] `lean/lean-toolchain`, `lean/lake-manifest.json` — toolchain/
      dependency lockfiles, not hand-written; skim only.
- [ ] `lean/setup.sh` — one-time local setup (`elan`, `lake update`,
      `lake exe cache get`).
- [ ] `.github/workflows/lean-test.yml` — new CI job: installs `elan`,
      fetches Mathlib's cache, runs `lake build` on `lean/**` changes.
- [ ] `python/pyproject.toml`, `python/uv.lock` — new dependencies
      (`jsonschema` for the schema test, presumably); check nothing
      unexpected snuck in.
- [ ] `.gitignore` (1 line changed) — quick look.
- [ ] `README.md` (+41/−changed) — repository-layout updates from both
      this and the previous documentation session.

---

**Note, unrelated to the plan itself:** `python/uv.lock` and
`lean/lake-manifest.json` are lockfiles — worth confirming your review
tooling doesn't try to diff them line-by-line the same way as
hand-written code.
