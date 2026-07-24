# Certifying spanning-tree-modulus optimality

This directory documents a pipeline that turns the C++ solver's output for
spanning tree modulus into a **certificate**: a machine-checkable proof,
checked by an independent Lean 4 program, that a given density/pmf pair is
optimal. The certificate lets us trust the answer without trusting the
solver's arithmetic.

## Why

`cpp/`'s `spt_mod` computes the exact spanning tree modulus of a graph. What
it returns is the optimal expected-edge-usage vector $\eta^*$, corresponding
to a probability mass function (pmf) on spanning trees that solves the dual
problem to modulus. This pmf can be transformed into the optimal edge density
$\rho^*$ for modulus, and vice versa. The solver's algorithm has been proved
correct by hand, but the C++ implementation itself is not formally verified.
The goal here is to produce, alongside the solver's answer, an artifact that
lets someone with no reason to trust that program confirm the answer
independently, checked by a kernel that trusts only a small, explicit,
documented set of axioms.

This is the standard **certifying algorithm** pattern: the solver and every
downstream tool that builds the certificate can be buggy or sloppy, and the
worst that happens is a rejected certificate. Only the Lean verifier needs to
be trusted, and it should accept a certificate only when it can prove
optimality.

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

Only the last stage needs to be correct for an accepted result to be *sound*.
The first two stages only need to be correct for a certificate to exist at
all: a bug in either one produces a certificate the verifier rejects, not a
false positive.

| Stage | Directory | Trusted? | What it does |
|---|---|---|---|
| Solver | `cpp/` | No | Computes $\eta^* \propto \rho^*$ and (with `--trace`) records the sequence of decisions Cunningham's algorithm made. |
| Builder | `python/src/discrete_modulus/` | No | Reconstructs a probability distribution over spanning trees from the solver's trace, and packages it into a certificate JSON file. |
| Verifier | `lean/` | Yes | Parses the certificate, constructs the pmf and density in Lean in rational arithmetic, and formally verifies that the pmf and density are optimal using strong duality. This is a kernel-checked proof that the certificate is valid. |

> [!WARNING]
> For now there is one exception to the "only the verifier needs to be
> trusted" principle. It is documented in [`trust.md`](trust.md).

## Reading order

1. **[`walkthrough.md`](walkthrough.md)**: the house graph, start to finish.
   What file gets produced at each stage, and what the verifier's output
   looks like. Read this first; it shows *what* happens before the rest of
   this directory explains *how* and *why*.
2. **[`pipeline.md`](pipeline.md)**: each stage in detail. What the solver
   records, how the builder reconstructs a pmf, and how the verifier is
   structured internally.
3. **[`schema.md`](schema.md)**: field-by-field reference for the two JSON
   formats involved (the solver trace and the certificate).
4. **[`trust.md`](trust.md)**: the trusted computing base. What's
   kernel-checked, what's accepted as trusted and why, and what remains as
   future work to close that gap.

## Where things live

- `cpp/include/discrete_modulus/solver_trace.hpp`: the solver-trace format
  and its writer.
- `cpp/include/discrete_modulus/cunningham.hpp`: the solver itself
  (`spanning_tree_modulus`), which can emit a trace when asked.
- `python/src/discrete_modulus/certificate_builder.py`: reads a trace plus
  the original graph and produces a certificate.
- `python/src/discrete_modulus/core_deflation.py`, `pmf_construction.py`,
  `tree_packing.py`: the pmf construction methods the builder calls.
- `lean/DiscreteModulusCert/`: the Lean verifier project; see `pipeline.md`
  for a per-file map.
- `docs/certification/certificate_schema.json`: the certificate format, as a
  machine-checkable JSON Schema (validated against in
  `python/tests/test_certificate_builder.py`).
