"""
Minimal-core detection and recursive deflation for spanning-tree modulus.

A graph `G` is (beta-)homogeneous when no vertex-induced subgraph has
strictly larger spanning-tree density `theta(H) = |E(H)| / (|V(H)| - 1)`
than `theta(G)` itself -- this is a hypothesis the C++ solver's own
correctness proof (Cunningham's algorithm) guarantees for every shrunk
multigraph it dispatches. Homogeneous graphs still split into two cases:
*strictly* homogeneous (every proper subgraph is strictly less dense --
no "forbidden trees", a uniform pmf on spanning trees can be built
directly, e.g. via `min_norm_point.min_norm_point_wolfe`) and merely
homogeneous (some proper subgraph -- the "core" -- ties `G`'s own
density, meaning some spanning trees would need negative weight to hit a
uniform marginal: "forbidden trees").

`find_core` locates the *minimal* tied proper subgraph (unique when one
exists) via an exact-integer max-flow construction (Goldberg's
densest-subgraph method, adapted from `|E|/|V|` to our `|E|/(|V|-1)`
density -- see the module-level notes below for the two traps that
adaptation runs into). `deflation_sequence` repeatedly finds and
contracts the top core until nothing is left but a rigid, strictly
homogeneous base -- the construction behind Theorem 8.1 of Albin, Lind,
Melikyan, Poggi-Corradini, "Minimizing the Determinant of the Graph
Laplacian" (`scratch/determinant_paper.pdf`): every core, once
contracted to a point, exposes a new (smaller) core one level down,
terminating at a rigid base with no forbidden trees at all.

Why not a direct continuous optimization (the paper's own minimum-
determinant formulation)? Prototyped first (`scratch/core_deflation.py`,
not carried into the package): it correctly identifies cores via where
the optimizer's edge log-weights diverge, but the divergence-detection
step (comparing solves at two floating-point tolerances) is unreliable
in practice -- the exact analytic gradient converges far too precisely
for a "does this keep drifting" heuristic to separate genuine divergence
from settled convergence. The max-flow construction here has no such
numerical-tolerance problem: every capacity is an exact integer.

Adapting Goldberg's construction from `|E(S)|/|S|` to `|E(S)|/(|S|-1)`
hits two traps, both handled below:

1. An unconstrained min cut always degenerates to the empty set (its
   cut value is fixed at `m*n`, strictly below what any nonempty set can
   achieve once the "-1" is accounted for) -- so at least one vertex
   must be forced onto the source side. But forcing a single vertex
   isn't enough either: singletons *vacuously* tie under this density
   (`|E({v})| - g*(1-1) == 0` for every v, regardless of `g`), so the
   fix is to force in a whole *edge* (both endpoints), which does not
   vacuously tie for any graph denser than a tree.
2. `networkx.minimum_cut`'s returned partition is the *maximal*
   minimizer (nodes that cannot reach the sink), not the minimal one --
   confirmed by reading its source: it computes reachability *to* the
   sink on the pruned residual graph. The minimal minimizer (which is
   what picks out a genuine smaller core instead of falling back to the
   whole graph) has to be computed by hand, as vertices reachable *from*
   the source in a properly-conserved max flow's residual graph (not
   `preflow_push`'s `value_only=True` mode, whose returned "flow" is a
   preflow with leftover excess near the source that makes this
   unreliable).

Nested ties are real, not a bug: e.g. in a multi-level "house" graph
built by stacking self-similar 4-cycle stories under a triangular roof,
every top-down suffix of stories ties at the same density as the whole
graph. Different anchor edges can therefore reveal different (and
differently sized) tied supersets containing them; recursing into
whatever tied set is found first correctly shrinks down to the true,
unique minimal core (justified by the lattice/intersection-closure of
tied sets under the graphic matroid's rank submodularity), but is only
*fast* if the first-tried anchor edge happens to land close to that
minimal core -- empirically this can be edge-order sensitive enough to
force many sequential single-story peels (an adversarial ordering
measured roughly cubic overall in the number of stories). Real
solver-dispatched shrunk multigraphs are not expected to nest this
deeply; revisit if that assumption doesn't hold up in practice.
"""

from __future__ import annotations

import networkx as nx


def find_core(G: nx.Graph) -> set[frozenset] | None:
    """
    Finds the minimal core of `G`: the unique minimal proper,
    vertex-induced subgraph whose spanning-tree density
    `|E(H)| / (|V(H)| - 1)` ties `G`'s own density `theta(G)`.

    Parameters
    ----------
    G : networkx graph
        A simple, connected, homogeneous graph (theta(H) <= theta(G) for
        every vertex-induced H) with at least 3 vertices and one edge --
        the shape of a shrunk multigraph dispatched by the solver, minus
        parallel edges (parallel edges never affect which vertex subset
        is densest, only which spanning trees exist on top of it, so
        callers with a multigraph should pass its underlying simple
        graph here).

    Returns
    -------
    set of frozenset, or None
        The core's edges (each a `frozenset({u, v})`), or `None` if `G`
        is strictly homogeneous (no proper subgraph ties `theta(G)`).
    """

    nodes = list(G.nodes())
    n = len(nodes)
    m = G.number_of_edges()
    if n < 3 or m == 0:
        return None

    deg = dict(G.degree())

    # g = theta(G) = m / (n - 1); every capacity below is scaled by
    # (n - 1) to keep this exact in integers: s->v becomes m*(n-1), v->t
    # becomes m*(n+1) - (n-1)*deg(v), and each edge arc becomes (n-1).
    s, t = "__source__", "__sink__"
    cap_sv = m * (n - 1)
    big = cap_sv * n * 10 + 1  # exceeds any achievable cut value

    for u0, v0 in G.edges():
        F: nx.DiGraph = nx.DiGraph()
        F.add_nodes_from(nodes)
        F.add_node(s)
        F.add_node(t)
        for v in nodes:
            F.add_edge(s, v, capacity=(big if v in (u0, v0) else cap_sv))
            cap_vt = m * (n + 1) - (n - 1) * deg[v]
            F.add_edge(v, t, capacity=cap_vt)
        for a, b in G.edges():
            F.add_edge(a, b, capacity=n - 1)
            F.add_edge(b, a, capacity=n - 1)

        _flow_value, flow_dict = nx.maximum_flow(F, s, t, capacity="capacity")
        residual: nx.DiGraph = nx.DiGraph()
        residual.add_nodes_from(F.nodes())
        for a, b, data in F.edges(data=True):
            cap = data["capacity"]
            fl = flow_dict[a][b]
            if cap - fl > 0:
                residual.add_edge(a, b)
            if fl > 0:
                residual.add_edge(b, a)
        core_vertices = nx.descendants(residual, s)

        if 0 < len(core_vertices) < n:
            core_edges = {
                frozenset((a, b)) for a, b in G.edges() if a in core_vertices and b in core_vertices
            }
            if core_edges:
                # This tied set might not be minimal (nested ties): recurse
                # into it to look for a smaller one before returning.
                smaller = find_core(G.subgraph(core_vertices))
                return smaller if smaller is not None else core_edges

    return None


def deflation_sequence(G: nx.Graph, verbose: bool = False) -> list[set[frozenset]]:
    """
    Repeatedly finds and contracts the top core of `G` (Theorem 8.1's
    deflation process) until a rigid, strictly homogeneous base is left.

    Parameters
    ----------
    G : networkx graph
        See `find_core`.

    verbose : bool
        If True, prints each level's core (or the terminating rigid
        base) as it's found.

    Returns
    -------
    list of set of frozenset
        The cores found, outermost first, each expressed in `G`'s
        original vertex labels.
    """

    cores: list[set[frozenset]] = []
    current = G.copy()
    represents: dict = {v: {v} for v in G.nodes()}

    level = 0
    while True:
        core = find_core(current)
        if core is None:
            if verbose:
                print(
                    f"level {level}: rigid base, {current.number_of_nodes()} vertices, "
                    f"{current.number_of_edges()} edges"
                )
            break

        core_vertices: set = set()
        for e in core:
            core_vertices |= set(e)

        orig_edges: set[frozenset] = set()
        for e in core:
            u, v = tuple(e)
            orig_edges |= {
                frozenset((ou, ov))
                for ou in represents[u]
                for ov in represents[v]
                if G.has_edge(ou, ov)
            }
        cores.append(orig_edges)
        if verbose:
            print(
                f"level {level}: core with {len(core_vertices)} vertices, "
                f"{len(orig_edges)} original edges"
            )

        new_point = f"__core_{level}__"
        contracted = current.copy()
        core_list = list(core_vertices)
        for v in core_list[1:]:
            contracted = nx.contracted_nodes(contracted, core_list[0], v, self_loops=False)
        contracted = nx.relabel_nodes(contracted, {core_list[0]: new_point})
        current = contracted

        merged: set = set()
        for v in core_vertices:
            merged |= represents[v]
        represents = {v: represents[v] for v in current.nodes() if v != new_point}
        represents[new_point] = merged

        level += 1
        if level > current.number_of_nodes() + len(G):
            raise RuntimeError("deflation did not terminate")

    return cores
