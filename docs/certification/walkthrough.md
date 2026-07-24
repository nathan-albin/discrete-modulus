# Worked example: the house graph, start to finish

This file demonstrates the whole pipeline on the smallest real example checked
into the repository, `cpp/examples/house`, showing the file contents produced at
each stage. You can reproduce all of it yourself (commands are given at each
step). The commands assume you have built the C++ solver as described in
[`cpp/README.md`](../../cpp/README.md) and have the repo's root directory as
your current working directory. See [`pipeline.md`](pipeline.md) for *why* each
stage works the way it does, and [`schema.md`](schema.md) for the full field
reference of the two JSON formats involved.

## 0. The graph

`cpp/examples/house.edges`:

```
5
0 1
1 2
2 3
3 4
4 0
1 4
```

5 vertices, 6 edges: a square (`1`–`2`–`3`–`4`) with a triangular roof
(`0`–`1`–`4`) sharing the edge `{1, 4}`.

## 1. Run the solver, with tracing

```
cpp/build/spt_mod cpp/examples/house --trace
```

This writes `house.eta` (the plain per-edge $\eta^*$ output every caller
gets) and, because of `--trace`, `house.trace.json`:

```json
{
  "version": 1,
  "rounds": [
    {
      "vertices": [0, 1, 2, 3, 4],
      "crit_set": [[3, 4], [2, 3], [1, 4], [0, 1], [1, 2], [0, 4]],
      "theta": [2, 3]
    }
  ]
}
```

House needs only one round: Cunningham's algorithm finds a single tight set
covering the whole graph, dispatching all 6 edges at once with $\theta = 2/3$. A
more complex graph that needs several rounds would have one entry in `"rounds"`
per round; see `pipeline.md` for a multi-round example. `house.eta` confirms
$\eta^* = 2/3$ on all six edges; the house is a *homogeneous* graph.

## 2. Build the certificate

```
python -m discrete_modulus.certificate_builder cpp/examples/house
```

This reads `house.edges` + `house.trace.json` and writes
`house.certificate.json`. Here's a slightly reformatted version of that file. The content is the same, but the whitespace is edited for readability:

```json
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
          { "edges": [0, 1], "weight": [1, 3] },
          { "edges": [0, 2], "weight": [1, 3] },
          { "edges": [1, 2], "weight": [1, 3] }
        ]
      }
    },
    {
      "edges": [3, 4, 5],
      "vertices": ["__core_0__", "2", "3"],
      "local_pmf": {
        "trees": [
          { "edges": [3, 5], "weight": [1, 3] },
          { "edges": [3, 4], "weight": [1, 3] },
          { "edges": [4, 5], "weight": [1, 3] }
        ]
      }
    }
  ],
  "eta":  [[2,3],[2,3],[2,3],[2,3],[2,3],[2,3]],
  "rho":  [[1,4],[1,4],[1,4],[1,4],[1,4],[1,4]]
}
```

**Why two pieces, for a single-round graph.** Even though the house is
homogeneous (so the solver completes in one round), it's not *strictly*
homogeneous. This causes a problem when we try to build the optimal pmf because
there are "forbidden trees" that we need to avoid. By first shrinking the roof
"core" triangle to a vertex, the builder produces two pieces that are both
strictly homogeneous, making it possible to produce the optimal pmf as a product
of the two pieces' pmfs. The builder's deflation step (`core_deflation.py`) is
the part that detects the roof triangle and shrinks it.

Both pieces are 3-edge triangles, so each has exactly 3 spanning trees (leave
one edge out). Assigning each tree a probability of $1/3$ gives a uniform value
of $\eta^*=2/3$ on each edge. To build a spanning tree of the house with this
distribution; pick one of piece 1's 3 trees and one of piece 2's 3 trees
independently, then take the union. Because of the way the pieces were constructed, this always produces a spanning tree of the house graph.

**`eta`/`rho` are checked, not trusted.** The builder computes these values
independently from `pieces` (summing each declared tree's weight into every edge
it touches) and puts them into the certificate. The `validate_certificate`
function re-derives them and asserts they match before writing the file. (Later,
the Lean verifier repeats that same check from scratch.)

## 3. Verify it in Lean

```
cd lean
lake exe verify_cert ../cpp/examples/house.certificate.json
```

```
../cpp/examples/house.certificate.json: ACCEPTED
  NOTE: admissibility of rho relies on an unverified Kruskal implementation
  (its output is trusted, not proven, to be a genuine minimum-weight spanning tree).
```

During this stage, the verifier:

1. Re-checks every piece: the declared spanning trees are actually spanning
   trees, the pmf weights are nonnegative and sum to 1, the pieces' edges disjointly cover the whole graph.
2. Recomputes `eta` and `rho` from `pieces` and confirms they match the
   declared fields.
3. Runs Kruskal's algorithm with the recomputed `rho` and confirms the
   minimum-weight spanning tree has weight $\ge 1$. For the house, every
   spanning tree has exactly 4 edges, and $\rho^*=1/4$ on every edge, so every spanning tree has weight exactly $1$.
4. Concludes optimality via the Cauchy-Schwarz duality argument
   (`Optimality.lean`'s `certificate_optimality`): $\rho$ pairs against $\eta$
   to exactly $1$ ($\left<\rho,\eta\right> = 6 \times \tfrac14 \times
   \tfrac23 = 1$), and $\|\rho\|^2 \|\eta\|^2 = \tfrac38 \times \tfrac83 = 1$. Cauchy-Schwarz is satisfied with equality, proving that $\rho$ and $\mu$ are both optimal.

`ACCEPTED` means the certificate has been validated by the Lean validator. You
can also see `lean/DiscreteModulusCert/EndToEndTest.lean`'s
`house_end_to_end_optimal` for an example of how to build a kernel-checked Lean
theorem stating the correctness conclusion for a certificate read from a JSON
file. See [`pipeline.md`](pipeline.md) for how the verifier is put together, and
[`trust.md`](trust.md) for exactly what "kernel-checked" does and doesn't mean
here (the Kruskal caveat above is the one exception).
