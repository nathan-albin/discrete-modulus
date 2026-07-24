# The pipeline, in detail

This file describes each of the three stages from [`README.md`](README.md), naming the files and functions responsible at each stage. You may want to read [`walkthrough.md`](walkthrough.md) first if you haven't, since it shows an end-to-end example of what each stage looks like on a real graph.

## 1. Solver instrumentation

**Files:** `cpp/include/discrete_modulus/cunningham.hpp`, `cpp/include/discrete_modulus/solver_trace.hpp`.

`spanning_tree_modulus` (`cunningham.hpp`) computes spanning tree modulus by repeatedly extracting a *tight set*: a subset of edges `crit_set` whose induced density exactly equals the current subproblem's vulnerability, `theta`, using the fact that $\eta^* = \theta$ on these edges. The function then recurses on whatever components remain once `crit_set` is removed. See the companion book's "Exact Spanning Tree Modulus" chapter for the underlying theory of why this recursion works.

The certificate builder needs to replay this decomposition without re-running the solver, so `spanning_tree_modulus` takes an optional `SolverTrace* trace` parameter. When non-null, the solver appends one `TraceRound` per round, defining the component's vertex set, the `crit_set` dispatched, and the corresponding `theta`. `write_trace_json` serializes the whole `SolverTrace` as `<prefix>.trace.json` (schema: see [`schema.md`](schema.md)). Vertex ids in the trace are the *original* graph's vertex descriptors, so the trace is self-contained.

For now, `spanning_tree_modulus` assumes its input is a simple graph (`graphs.hpp`'s `is_simple_graph`).

## 2. Certificate builder

**Files:** `python/src/discrete_modulus/certificate_builder.py`, `core_deflation.py`, `pmf_construction.py`, `tree_packing.py`.

For each round of the trace, `certificate_builder.py` takes the following steps:

1. **Reconstructs the round's own working graph** exactly, as `g.subgraph(round.vertices)`. 

2. **Shrinks it**: each of the components that would remain after removing `crit_set` is contracted to a single vertex, leaving only the `crit_set` edges connecting them. Parallel edges are kept intact, so the result is a multigraph in general.

3. **Builds a pmf on this shrunk multigraph's spanning trees** (See `pmf_construction.build_factored_pmf` in the next section.) While this multigraph is known to be homogeneous, the Cunningham-based solver doesn't produce an optimal pmf directly, so the certificate builder constructs one at this stage.

4. **Translates local edge indices to global ones** and appends the result to the certificate's `pieces` list, **in reverse round order**. The modulus solver processes the outermost tight set first and recurses inward, but building the pmf is easier from the perspective of *deflation*, building outward from the innermost homogeneous core.

### Building the pmf for one (multi)graph: deflation + tree packing

When viewed from the deflation perspective, every shrunk multigraph the solver dispatches is *homogeneous*: no vertex-induced subgraph has strictly larger density $|E(H)|/(|V(H)|-1)$ than the graph itself. There are two flavors of homogeneous multigraphs:

- **Strictly homogeneous** (every proper subgraph is strictly less dense): there exists an optimal pmf that contains every spanning tree in its support; i.e., there are no "forbidden trees." 

- **Merely homogeneous**: some proper subgraph has the same density as the whole graph (a core). That means that some spanning trees are "forbidden" in the sense that they aren't allowed in any optimal pmf. This causes problems for the builder, so we need to further decompose these into strictly homogeneous pieces.

`core_deflation.py`'s `find_core` locates a strictly homogeneous core, shrinks it away, and repeats until only a strictly homogeneous shrunk graph remains.

Each resulting piece (a core, or the final rigid base) is strictly homogeneous with vulnerability `theta = p/q` in lowest terms. This gives us a *tree packing* problem: find `q` spanning trees such that every edge is used in exactly `p` of them, assign a probability of `1/q` to each tree. `tree_packing.build_tree_packing` constructs this directly, by a two-tier local search (an away-step tree-for-tree swap that provably never increases the coverage-imbalance energy, falling back to a BFS matroid-exchange search when the swap alone stalls).

> [!WARNING]
> I don't have a proof of the tree-packing property yet. Namely, I haven't proved that a strictly homogeneous multigraph with rational vulnerability `p/q` always has a tree packing of size `q` that covers every edge exactly `p` times. It's a pattern I noticed in several examples and the builder seems to find one every time, but I don't have a proof that it always exists. If you know of a proof or find a counterexample, please let me know. Importantly, this doesn't affect the soundness of the verifier. In the worst case, the builder will simply fail to build a certificate.

The result, `pmf_construction.FactoredPmf`, represents the whole distribution in a *factored* form. Each core of the recursively deflated graph has its own local pmf. The full pmf is the product of these local pmfs, which can be thought of as follows. Choose a spanning tree for each piece independently according to its own local pmf, then take the union of the edges selected. This works because the pieces partition the graph's edges and because of the way in which the pieces nest during deflation. This factored shape is recorded in the certificate's `pieces` array. It's important to factor the pmf this way. If, instead, we were to build a single global pmf from these pieces, it would have a support size that is the product of the support sizes of each piece's local pmf, giving an exponential blowup in the size of the certificate.

### Sanity checks on `eta` and `rho`

`compute_eta_from_pieces` accumulates the weight of each tree in the factored pmf into a global marginal $\eta$ as it progresses. It also computes $\rho$ via `compute_rho`, which just calculates $\rho = \eta / \|\eta\|^2$. `validate_certificate` re-derives both from `pieces` and asserts they match the certificate's own declared fields before the builder writes the file. This gives a cheap sanity check for the builder before we pass the certificate along to the more expensive Lean verifier stage.

## 3. The Lean verifier

**Directory:** `lean/DiscreteModulusCert/`. Depends on [`lean-modulus`](https://github.com/nathan-albin/lean-modulus) (pinned to a specific commit) for its graph/matroid infrastructure (`Multigraph`, `graphicMatroid`).

### The math: Cauchy-Schwarz duality (`Optimality.lean`)

Although the general $p$-modulus duality theory relies on convex analysis and uses Lagrangian duality arguments, $2$-modulus is special: the duality can be expressed in terms of the Cauchy-Schwarz inequality. Let $\mathcal{N}$ be the usage matrix for spanning trees (each row is an incidence vector of a spanning tree). A density $\rho\in\mathbb{R}^E_{\ge 0}$ is admissible if $\mathcal{N}\rho \ge 1$ (every spanning tree has $\rho$-weight $\ge 1$). If $\mu$ is a pmf on spanning trees with marginal $\eta = \mathcal{N}^T\mu$ on the edges, then

$$
\left<\rho,\eta\right> = \left<\rho,\mathcal{N}^T\mu\right> = \left<\mathcal{N}\rho,\mu\right> \ge 1.
$$

Applying Cauchy-Schwarz gives

$$
1 \le \left<\rho,\eta\right> \le \|\rho\| \|\eta\|,
$$

and minimizing over admissible $\rho$ and $\mu$ gives the weak duality bound. To demonstrate that a pair $(\rho,\mu)$ are optimal for their respective problems, it suffices to show that equality holds in the Cauchy-Schwarz inequality, which happens exactly when $\rho = \eta / \|\eta\|^2$.

`certificate_optimality` (`Optimality.lean`) is the Lean formalization of this argument. It uses a specially built `ℚ`-valued version of the argument instead of relying on the `lean-modulus` library, which is expressed in terms of `ℝ≥0`-valued densities.

### Gluing pieces into one pmf (`Glue.lean`)

A certificate's `pieces` array is a flat, ordered list of blocks in "deflation order." `Glue.lean` proves this is enough to reconstruct a complete pmf on the *whole* graph's spanning trees. `isBase_union_of_isBase_restrict_isBase_contract` is a general matroid fact: a base of a restriction to a block, plus a base of the contraction by that block, unions to a base of the whole matroid. This is lifted to `Pmf.glue` (gluing two pmfs), which folds down a whole `PieceList` via `glueAll`. Critically, `Pmf.glue_marginal`/`PieceList.glueAll_marginal` prove the glued pmf's marginal is exactly the *sum* of every piece's own local marginal, which is what allows the verifier to check the certificates declared `eta` and `rho` fields without actually constructing a full pmf.

### Reducing "is this a base" to "is this a forest" (`IsBaseCheck.lean`, `ForestDecide.lean`)

A certificate provides each piece's trees as a list of edges, but the Lean verifier needs to actually know that they are trees. Because of the deflation process (`isBase_contract_restrict_iff_isForest`), this reduces to two checks that can be performed directly on the original graph without any contraction or relabeling. If `I₀` is the already-verified representative tree of everything processed so far, and `T` is a candidate tree from the current piece, we need to check (a) is `I₀ ∪ T` a forest, and (b) is it maximal (no other edge of the piece can be added without creating a cycle).

### The runnable checker (`CertChecker.lean`, `Kruskal.lean`, `Admissibility.lean`)

`CertChecker.checkCertificate` is the executable entry point: parses a certificate JSON (`Lean.Data.Json` + `deriving FromJson`), folds `checkPiece`/`checkPieces` over `pieces` (each piece's forest/maximality/weight checks above), confirms the pieces partition the graph's edges, recomputes `eta`/`rho` and rejects on mismatch, and finally runs `Kruskal.run` (a plain greedy union-find MST implementation) against the recomputed `rho`, rejecting if the minimum spanning tree's weight is `< 1`. This is a plain executable, since the certificate's content is only known at runtime.

> [!IMPORTANT]
> `Admissibility.lean`'s `Kruskal.run_isAdmissible_of_weight_ge_one` is the one place trust enters the verifier pipeline. Mathlib currently does not contain a proof that Kruskal's algorithm is correct. What we need is to show that $\rho$ gives $\ge 1$ weight to every spanning tree, but what we really show is that Kruskal's algorithm finds a spanning tree of weight $\ge 1$. If Kruskal's algorithm is correct, the two are equivalent, but the Lean proof is missing. That gap is currently filled with an `axiom` rather than a proof; see [`trust.md`](trust.md).

### From "checker accepts" to a kernel-checked proof (`Soundness.lean`)

Running `checkCertificate` and getting `ok` back is solely a runtime fact and does not constitute a kernel-checked proof. To close that gap, `Soundness.lean` provides the theorem `checkCertificate_sound` that shows that if `checkCertificate` accepts a certificate, then there *exists* a `Pmf`/`PieceList` with the declared `rho` admissible and the declared `eta` exactly equal to the constructed pmf's marginal. This is done by threading the forest/maximality proofs through the fold of `checkPieces_sound`.

### A concrete instance (`EndToEndTest.lean`)

`EndToEndTest.lean`'s `house_end_to_end_optimal`/`nested_end_to_end_optimal` prove the full conclusion using the certificate files produced by the Python builder on the house/nested graphs.

### A couple of implementation notes

- **`native_decide` vs. `decide`.** Several checks (`Multigraph.IsForest` on real certificate data, the parsed-JSON end-to-end tests) use `native_decide` rather than `decide`: some of Mathlib's own decidability instances are built in a way the kernel's own reduction can't unfold, or are simply too slow for the kernel to evaluate on realistically-sized pieces. Since `native_decide` compiles and runs native code, it runs faster, but lands outside the kernel's proof-checking. This tradeoff is documented in [`trust.md`](trust.md).
- **No generic computable `E → Fin m` projection.** `CertChecker.lean`'s `sumTreeContributions` works directly over `Nat`-indexed raw JSON data rather than through the file's own generic `{V E} [Fintype E]` abstraction, because `Fintype.equivFin` is `noncomputable`; there is no way to turn an abstract `Fintype E` into a concrete `Fin m` index generically at runtime. This same obstacle shows up more than once in this codebase. 