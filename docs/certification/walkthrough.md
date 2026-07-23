# Worked example: the house graph, start to finish

This walks the whole pipeline on the smallest real example checked into
the repository, `cpp/examples/house`, showing the actual file contents
produced at each stage. Nothing here is simplified or made up for
exposition — every number below is exactly what the tools produce; you
can reproduce all of it yourself (commands are given at each step). See
[`pipeline.md`](pipeline.md) for *why* each stage works the way it does,
and [`schema.md`](schema.md) for the full field reference of the two JSON
formats involved.

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
(`0`–`1`–`4`) sharing the edge `{1, 4}` — the classic "house" pentagon.

## 1. Run the solver, with tracing

```
spt_mod cpp/examples/house --trace
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

House needs only one round: Cunningham's algorithm finds a single tight
set covering the whole graph, dispatching all 6 edges at once with
$\theta = 2/3$. (A graph that needs several rounds — because the solver
peels off one tight subset, then recurses on what's left — would have
one entry in `"rounds"` per round; see `pipeline.md` for a multi-round
example.) `house.eta` confirms $\eta^*_e = 2/3$ on all six edges — the
number every later stage has to reproduce and justify.

## 2. Build the certificate

```
python -m discrete_modulus.certificate_builder cpp/examples/house
```

This reads `house.edges` + `house.trace.json` and writes
`house.certificate.json`. In full (reformatted for readability; the real
file is more compact):

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

**Why two pieces, for a single-round graph.** The solver's single round
still isn't *strictly* homogeneous: the roof triangle `{0,1,4}`
(edges 0, 1, 2) ties the whole house's own spanning-tree density
($\theta_\triangle = 3/(3-1) = 3/2 = 6/(5-1) = \theta_{\text{house}}$),
so a uniform pmf over the *whole* house's spanning trees would need to
assign the triangle's edges impossible negative marginal — a "forbidden
tree" obstruction. The builder's deflation step (`core_deflation.py`)
detects this and peels the triangle off as its own piece first; what's
left (contract the triangle to one point, named `"__core_0__"`) is the
square `1`–`2`–`3`–`4` with `1` and `4` identified — itself another
3-edge/3-vertex triangle, and now genuinely rigid (piece 2 above).

Both pieces are 3-edge triangles, so each has exactly 3 spanning trees
(leave one edge out), each getting weight $1/3$ — the unique uniform
distribution with $\theta = (n-1)/m = (3-1)/3 = 2/3$ on a 3-vertex,
3-edge piece, matching the round's own recorded `theta`. A genuine
spanning tree of the whole house is built by picking one of piece 1's 3
trees *and* one of piece 2's 3 trees, independently, and taking the
union — always exactly 4 edges spanning all 5 vertices, since the pieces
share only the contraction point and partition the house's edges between
them.

**`eta`/`rho` are checked, not trusted.** The builder computes them
independently from `pieces` (summing each declared tree's weight into
every edge it touches) and the file ships both — `validate_certificate`
re-derives them and asserts they match before writing the file, and the
Lean verifier repeats that same check from scratch. Every edge gets
$\eta^*_e = 2/3$ (matching `house.eta` exactly) and
$\rho_e = \eta_e / \|\eta\|^2 = (2/3) / (8/3) = 1/4$.

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

Concretely, the verifier:

1. Re-checks every piece: its declared trees are genuine forests, each is
   maximal (no other edge of the piece can be added without creating a
   cycle), weights are non-negative and sum to 1, and the pieces'
   edges disjointly cover the whole graph.
2. Recomputes `eta` and `rho` from `pieces` and confirms they match the
   declared fields.
3. Runs Kruskal's algorithm against the recomputed `rho` and confirms the
   minimum-weight spanning tree has weight $\ge 1$ — here, every spanning
   tree has exactly 4 edges and $\rho \equiv 1/4$, so every tree (not just
   the minimum) weighs exactly $1$, admissible with no slack at all.
4. Concludes optimality via the Cauchy-Schwarz duality argument
   (`Optimality.lean`'s `certificate_optimality`): $\rho$ pairs against
   $\eta$ to exactly $1$ ($6 \times \tfrac14 \times \tfrac23 = 1$), and
   $\|\rho\|^2 \|\eta\|^2 = \tfrac38 \times \tfrac83 = 1$ — equality in
   Cauchy-Schwarz, which is exactly the condition under which $\rho$ and
   the pmf's marginal are *both* optimal.

This isn't just a printed "ACCEPTED": `lean/DiscreteModulusCert/EndToEndTest.lean`'s
`house_end_to_end_optimal` is a genuine, kernel-checked Lean theorem
stating exactly this conclusion for this real, on-disk certificate —
parsed by Lean's real JSON parser, not hand-transcribed. See
[`pipeline.md`](pipeline.md) for how the verifier is put together, and
[`trust.md`](trust.md) for exactly what "kernel-checked" does and
doesn't mean here (the Kruskal caveat above is the one exception).
