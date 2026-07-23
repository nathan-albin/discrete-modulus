# Certifying spanning-tree-modulus optimality

This directory documents a pipeline that takes the C++ solver's output for
spanning tree modulus and produces a **certificate**: a machine-checkable
proof, verified by an independent Lean 4 program, that a claimed-optimal
density/pmf pair really is optimal — without trusting the C++ solver's
arithmetic.

## Why

`cpp/`'s `spt_mod` computes the exact spanning tree modulus of a graph: an
admissible edge density $\rho^*$ and (implicitly) a probability
distribution over spanning trees, related by a duality argument. The
solver is fast, exact-rational, and reasonably well-tested — but it's
still one C++ program, and "trust the implementation" is not the same
thing as "proven correct." The goal here is to produce, alongside the
solver's answer, an artifact that lets someone with no reason to trust
that C++ program (or the tools that process its output) independently
confirm the answer is right, checked by a kernel that only trusts a small,
explicit, and documented set of axioms.

This is the standard **certifying algorithm** pattern: the solver and
every downstream tool that builds the certificate can be buggy, sloppy,
or actively adversarial, and the worst that happens is a rejected
certificate — never a false "verified" result. Soundness lives entirely
in the last stage, the Lean verifier.

## Architecture

```
 C++ solver (untrusted)                    cpp/
        │  produces a graph + a per-round solver trace
        ▼
 Certificate builder (untrusted)           python/src/discrete_modulus/
        │  builds a pmf on spanning trees, packages it as a certificate
        ▼
 Lean verifier (trusted)                   lean/
        │  parses the certificate, checks it in exact rational arithmetic,
        │  concludes optimality via a kernel-checked proof
        ▼
 ACCEPTED / REJECTED
```

Only the last box needs to be correct for a passing result to be
*sound*. The first two boxes only need to be correct for a certificate to
*exist* at all — a bug in either one produces a certificate the verifier
rejects, not a false positive.

| Stage | Directory | Trusted? | What it does |
|---|---|---|---|
| Solver | `cpp/` | No | Computes $\eta^* = \rho^*$ and (with `--trace`) records the sequence of decisions Cunningham's algorithm made. |
| Builder | `python/src/discrete_modulus/` | No | Reconstructs a genuine probability distribution over spanning trees from the solver's trace, and packages it with the graph into a certificate JSON file. |
| Verifier | `lean/` | Yes | Parses the certificate, checks every arithmetic invariant in exact rational arithmetic, and proves — as a kernel-checked theorem, not just a runtime check — that the certificate's density and pmf are simultaneously optimal. |

The one deliberate exception to "only the verifier needs to be trusted"
is documented in [`trust.md`](trust.md).

## Reading order

1. **[`walkthrough.md`](walkthrough.md)** — the house graph, start to
   finish: what file gets produced at each stage, and what the verifier's
   output looks like. Read this first — it shows *what* happens before
   the rest of this directory explains *how* and *why*.
2. **[`pipeline.md`](pipeline.md)** — each stage in detail: what the
   solver records, how the builder reconstructs a pmf, and how the
   verifier is structured internally.
3. **[`schema.md`](schema.md)** — field-by-field reference for the two
   JSON formats involved (the solver trace and the certificate).
4. **[`trust.md`](trust.md)** — the trusted computing base: what's
   kernel-checked, what's accepted as trusted and why, and what's tracked
   as future work to close that gap.

## Where things live

- `cpp/include/discrete_modulus/solver_trace.hpp` — the solver-trace
  format and its writer.
- `cpp/include/discrete_modulus/cunningham.hpp` — the solver itself
  (`spanning_tree_modulus`), instrumented to emit a trace when asked.
- `python/src/discrete_modulus/certificate_builder.py` — reads a trace
  plus the original graph, produces a certificate.
- `python/src/discrete_modulus/core_deflation.py`,
  `pmf_construction.py`, `tree_packing.py` — the pmf-construction
  machinery the builder calls into.
- `lean/DiscreteModulusCert/` — the Lean verifier project; see
  `pipeline.md` for a per-file map.
- `docs/certification/certificate_schema.json` — the certificate format,
  as a machine-checkable JSON Schema (validated against in
  `python/tests/test_certificate_builder.py`).
