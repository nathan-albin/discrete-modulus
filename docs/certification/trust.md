# Trusted computing base

The honest answer to "what would have to be broken for a bad certificate
to verify." Keep this current — it's meant to be checked, not taken on
faith.

| Component | Trusted? | Notes |
|---|---|---|
| Lean 4 kernel + Mathlib axioms | Yes | Standard, unavoidable for any Lean proof. |
| `lean-modulus`'s `Common/` definitions (pinned commit) | Yes, but low-risk | The *proofs* (matroid axioms, rank-nullity, etc.) are kernel-checked regardless of which repo they live in. The *definitions* (`Multigraph`, `IsSpanningTree`, `graphicMatroid`, ...) carry ordinary formalization-adequacy risk: worth a sanity check that they mean what's intended, same as any definition written from scratch. The pinned commit (`lean/lakefile.toml`) makes exactly which version this rests on auditable. |
| `Family.lean`'s own `CertDensity`/`Pmf`/`IsAdmissible` vocabulary | Yes, but low-risk | Defined fresh (not reused from `lean-modulus`) because `lean-modulus`'s own `ℝ≥0`-valued `Density`/`Adm` can't state Cauchy-Schwarz directly (`ℝ≥0` has no subtraction). Same formalization-adequacy caveat as above. |
| The duality theorem (`Optimality.lean`'s `certificate_optimality`) | Yes, by construction | Proved once, kernel-checked — a small, self-contained Cauchy-Schwarz argument, not routed through `lean-modulus`'s heavier extreme-points/compactness machinery. |
| Certificate parsing / arithmetic checks (`CertChecker.lean`, `Soundness.lean`) | Yes, by construction | This is the "explicit verification" step — all in exact `ℚ` arithmetic, and `Soundness.lean` proves the runtime checker's `ok` result really does imply a genuine, optimal `Pmf` exists (not just that the checker ran without error). |
| `native_decide`'s compiler trust | Yes, but standard | Several checks (real certificate data against `Multigraph.IsForest`, the parsed-JSON end-to-end tests) use `native_decide` rather than `decide`, because some Mathlib decidability instances don't reduce in the kernel, or are too slow there on realistically-sized data. This trusts the Lean compiler's code generation (`Lean.ofReduceBool`) for that specific check, not just the kernel — standard practice, and a much narrower trust surface than trusting arbitrary external code, but a real one, distinct per callsite (shows up by name under `#print axioms`). |
| Kruskal's algorithm (`Kruskal.lean`) | **No — the one accepted gap** | See below. |
| C++ solver (`cpp/`) | No | Only a source of candidate certificates; a bug here produces a rejected certificate, not a false "verified" result. |
| Certificate builder (`python/`) | No | Same — untrusted, can be sloppy/buggy without compromising soundness. |

## The one accepted gap: Kruskal's algorithm

Checking a density $\rho$ is admissible (every spanning tree has
$\rho$-weight $\ge 1$) reduces to checking the *minimum*-weight spanning
tree's weight is $\ge 1$ — if the minimum clears the bar, every tree does;
if some tree didn't, it couldn't be less than the true minimum. Finding
that minimum is exactly what Kruskal's algorithm computes. `Kruskal.lean`
implements the standard greedy algorithm (sort edges by weight, keep each
that joins two still-separate union-find components) — but its
correctness (that the greedy algorithm's output really *is* a minimum
spanning tree) is not proved; the result is trusted, not proven.

This is made an explicit, named `axiom`
(`Admissibility.lean`'s `Kruskal.run_isAdmissible_of_weight_ge_one`)
rather than an implicit gap, so it shows up by name under `#print axioms`
for any certificate whose `rho` isn't uniform. (A certificate with a
uniform `rho` — like the house example in `walkthrough.md` — needs no
such axiom: `Admissibility.lean`'s `isAdmissible_const_div_ncard_of_isBase`
proves admissibility directly from a basic matroid fact, every base has
the same cardinality, without trusting an MST oracle at all -- a check
that the axiom really is avoidable when it can be.)

Reframed precisely: this is *not* "we've approximated what admissibility
means" — `isAdmissible_iff_one_le_pairing_usageVector` (`Optimality.lean`)
shows admissible ⟺ minimum base weight $\ge 1$ exactly. The gap is
narrowly "we trust this specific greedy implementation to compute that
minimum correctly." `lake exe verify_cert` prints this caveat
unconditionally alongside every `ACCEPTED` result, not just here.

**Closing it** would mean proving the matroid greedy-exchange theorem,
specialized to the graphic matroid, in Lean — a genuine "hard Lean
project" in its own right, not yet attempted. It's independent of
everything else in this pipeline: nothing here needs to be re-architected
when it lands, it would simply replace the axiom with a proof.

## What this buys you

For a certificate whose `rho` is uniform, an `ACCEPTED` result from
`verify_cert` is a fully kernel-checked proof (Lean kernel + Mathlib
axioms only) that the certificate's density and pmf are simultaneously
optimal — no trust in the C++ solver, the Python builder, or an external
MST implementation anywhere in the chain. For a certificate whose `rho`
isn't uniform, the same holds *modulo* trusting that `Kruskal.run`
correctly computes a minimum spanning tree — a narrow, explicit,
well-understood algorithm, not the C++ solver's own (much larger and
more complex) implementation.
