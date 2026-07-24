# JSON formats

Two JSON formats are involved in the pipeline: the **solver trace**
(`spt_mod`'s `--trace` output, consumed only by the certificate builder)
and the **certificate** (the builder's output, consumed by the Lean
verifier). Both use `[numerator, denominator]` pairs of arbitrary-precision
JSON integers for every rational number. Never floating point, and never
assume the 53-bit-safe integer range: numerators and denominators come
from exact `Fraction` arithmetic on the Python side and can be large. A
JSON parser that silently coerces big integers to double-precision floats
will silently corrupt either format.

See [`walkthrough.md`](walkthrough.md) for both formats populated with
real numbers from the house example.

## Solver trace (`<prefix>.trace.json`)

Written by `write_trace_json` (`cpp/include/discrete_modulus/solver_trace.hpp`),
parsed by `parse_solver_trace` (`certificate_builder.py`). There is no
separate machine-checkable schema file: the format is small enough that the
C++ struct (`TraceRound`/`SolverTrace`) and the Python dataclasses
(`TraceRound`/`SolverTrace` in `certificate_builder.py`) are the
authoritative definitions, kept in sync by hand.

```jsonc
{
  "version": 1,
  "rounds": [
    {
      "vertices": [0, 1, 2, 3, 4],   // this round's component, as ORIGINAL graph vertex ids
      "crit_set": [[3, 4], [2, 3]],  // dispatched edges, as [u, v] original vertex-id pairs
      "theta": [2, 3]                // [numerator, denominator]: this round's eta*/theta value
    }
  ]
}
```

| Field | Meaning |
|---|---|
| `version` | Currently always `1`. Independent of `certificate_version` below: the two formats evolve on different schedules. |
| `rounds` | One entry per round of the solver's main loop, in dispatch order (outermost tight set first). |
| `rounds[i].vertices` | The component this round was carved from, as a list of the *original* input graph's vertex ids (not a round-local renumbering). |
| `rounds[i].crit_set` | The tight set of edges dispatched this round, as `[u, v]` pairs of original vertex ids. |
| `rounds[i].theta` | This round's $\theta$ (equivalently, $\eta^*$ on every edge in `crit_set`), as `[numerator, denominator]`. |

**Known fidelity gap.** `crit_set` identifies edges by their endpoint
*vertex pair*, not a stable edge id. This is unambiguous for any graph
without true parallel edges (every example currently checked in) but is a
latent gap for the general multigraph case: two parallel edges between
the same pair of vertices can't be told apart from `crit_set` alone. The
certificate's own top-level `graph.edges` (below) correctly preserves
distinct parallel edges by array position; it only affects translating a
trace's `crit_set` into certificate edge indices for a graph that actually
has parallel edges. Not yet fixed; would need `crit_set` to carry each
edge's stable `edge_index` (already tracked internally by
`cunningham.hpp`) alongside or instead of the vertex pair.

## Certificate (`<prefix>.certificate.json`)

Machine-checkable schema (JSON Schema, Draft 2020-12):
[`certificate_schema.json`](certificate_schema.json). Written by
`certificate_builder.build_certificate`, parsed by
`CertChecker.RawCertificate` (`lean/DiscreteModulusCert/CertChecker.lean`,
via `Lean.Data.Json` + `deriving FromJson`), validated in Python by
`certificate_builder.validate_certificate`.

```jsonc
{
  "certificate_version": 5,
  "graph": {
    "num_vertices": 5,
    "edges": [[0, 1], [0, 4], [1, 4], [1, 2], [2, 3], [3, 4]]
  },
  "pieces": [
    {
      "edges": [0, 1, 2],
      "vertices": ["0", "1", "4"],
      "local_pmf": {
        "trees": [
          { "edges": [0, 1], "weight": [1, 3] }
        ]
      }
    }
  ],
  "eta": [[2, 3], [2, 3], [2, 3], [2, 3], [2, 3], [2, 3]],
  "rho": [[1, 4], [1, 4], [1, 4], [1, 4], [1, 4], [1, 4]]
}
```

| Field | Meaning |
|---|---|
| `certificate_version` | Currently always `5`. |
| `graph.num_vertices` | Vertices are the integers `0..num_vertices-1` (matches Boost's `vecS` vertex descriptor, so no separate label list). |
| `graph.edges` | `edges[i]` gives global edge `i`'s two endpoints. Array position **is** the edge's stable global index: every other `edges` list in the document indexes into this array, never relabeled. Parallel edges (repeated `[u, v]` pairs) are legal, distinct identities. |
| `pieces` | A **flat, ordered** list of blocks, one per within-round deflation core, or per solver round if it needed no further deflation. Order matters: it must be dependency order (see `pipeline.md`'s "reverse round order" note), the same order the builder itself produces. |
| `pieces[i].edges` | This piece's own edge scope, as global indices into `graph.edges`. Must be disjoint from every earlier piece's `edges`, and the union of all pieces' `edges` must be the whole `graph.edges` list (verifier-checked, not schema-checked). |
| `pieces[i].vertices` | **Informational only, never checked.** Original vertex ids and/or synthetic per-deflation-core labels (e.g. `"__core_0__"`, matching `pmf_construction.py`'s own naming). Every verifier check runs purely on edge sets. Kept for traceability back to the solver trace's own `vertices` field and for human debugging. |
| `pieces[i].local_pmf.trees` | This piece's local pmf: a list of `(tree, weight)` pairs, using global edge indices throughout (never piece-local; see below). |
| `pieces[i].local_pmf.trees[j].edges` | One spanning tree of this piece, as global edge indices (a subset of the enclosing piece's own `edges`). |
| `pieces[i].local_pmf.trees[j].weight` | This tree's probability, `[numerator, denominator]`. Must be non-negative; a piece's weights must sum to exactly `1` (verifier-checked). |
| `eta` | The optimal pmf's marginal at every edge (global index, same order as `graph.edges`). **Checked, not trusted**: the verifier recomputes it from `pieces` and rejects on mismatch. |
| `rho` | The admissible density $\rho = \eta / \|\eta\|^2$, same indexing. **Checked, not trusted**: recomputed from the (verified) `eta` and rejected on mismatch. |

**Why tree edges are global indices, not piece-local ones.** The Python
builder's own internal representation uses piece-local indices (dense,
`0..piece_size-1`, what the pmf-construction algorithms actually operate
on), but translating to global indices once, at emission time, means the
verifier never needs a local-to-global translation step at all:
`Multigraph.IsForest` and friends apply directly to a piece's declared
trees exactly as they would to the whole graph.

**Why `eta`/`rho` are shipped at all, given the verifier derives them
anyway.** The verifier's own combined pmf (`Pmf.glue`'s support) is a
literal Cartesian product over all pieces, exponential in piece count, so
it can never be computed directly either way; the verifier already has to
derive `eta`/`rho` compositionally from `pieces` regardless of what the
certificate declares. Since the derivation happens either way, shipping
the values and checking them against it costs nothing beyond that
derivation, and makes the certificate a self-contained, human/tool-readable
artifact: `eta`/`rho` are legible directly from the JSON file, and
directly diffable against the C++ solver's own `*.eta` output without
running the verifier at all.
