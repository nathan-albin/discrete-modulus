"""
Core detection via Goldberg's densest-subgraph max-flow construction,
adapted for our density metric theta(H) = |E_H| / (|V_H| - 1), replacing
core_deflation.py's continuous-optimization approach (which had a real
correctness bug: SLSQP's ftol-based divergence detection couldn't
reliably distinguish "still diverging" from "already converged").

Standard Goldberg construction (density = |E(S)|/|S|, target g): build a
flow network with source s, sink t, one node per vertex v of the current
graph, and

    s -> v          capacity m
    v -> t          capacity m + 2g - deg(v)
    u -> v, v -> u  capacity 1   (for every edge (u,v) of the graph)

Then, writing the s-side of a cut as {s} u S:

    cut(S) = m*n - 2*(|E(S)| - g*|S|)

so minimizing cut(S) is the same as maximizing |E(S)| - g|S|, and
min-cut < m*n  <=>  some nonempty S has |E(S)| - g|S| >= 0, i.e. density
|E(S)|/|S| >= g.

Our density is |E_H|/(|V_H|-1), not |E_H|/|V_H|. Substituting
g := theta(G) = m/(n-1) and asking for |E(S)| - g(|S|-1) >= 0 is the same
optimization (an additive constant g doesn't change the argmax), just a
shifted threshold: cut(S) <= m*n + 2g instead of cut(S) < m*n. Since
S = V always achieves cut(V) exactly m*n + 2g when g = theta(G) (the
whole graph trivially ties itself -- the tie the user flagged), the
network is identical to the standard one; only the "is this interesting"
threshold changes.

Tie-breaking (the actual fix for the house/roof ambiguity): the set of
min-cut minimizers of a submodular cut function forms a lattice, so
there is a well-defined MINIMAL minimizer and MAXIMAL minimizer. The
minimal one is "vertices reachable from s in the residual graph after
max-flow" -- NOT what nx.minimum_cut returns (its source, checked
directly, computes reachability *to* t on the pruned residual graph,
which is the MAXIMAL minimizer -- the opposite of what we need). We
compute the minimal side by hand from a properly-conserved max flow
(nx.maximum_flow, not preflow_push's value_only=True mode, whose
returned "flow" is a preflow with leftover excess near s that makes the
residual graph unreliable for this).

A second wrinkle: minimizing over ALL S (including S=empty and
singletons) doesn't work, because our density's "-1" makes singletons
*vacuously* tied (|E({v})| - g*(1-1) = 0 regardless of g) and S=empty
always beats S=V outright (cut(empty)=mn < cut(V)=mn+2g whenever g>0).
Fix: anchor on an EDGE (force both endpoints source-side via
cap(s,v)=infinite), which excludes both degeneracies since a forced
pair only scores 1-g, not 0.

Nested ties are also real (not a bug): e.g. in the multi-level house
family, stacking whole levels preserves the same density as the full
graph, so different anchor edges can reveal different (differently
sized) tied supersets containing them. Recursing into whatever tied set
is found first correctly shrinks to the true unique minimal core
(justified by the lattice/intersection-closure of tied sets under
matroid-rank submodularity), but is only fast if the first-tried anchor
happens to land close to the true core -- confirmed empirically to be
edge-order sensitive (a specific graph-construction order can force
O(m) sequential single-story peels, cubic overall; a well-chosen order
finds the true core directly). Fine for graphs up to ~100-150 vertices;
revisit if real modulus instances turn out to need more.

Everything is done with exact integer capacities (scale by (n-1) to
clear the g = m/(n-1) fraction) so this has none of the floating-point
convergence issues the SLSQP approach had.
"""

from __future__ import annotations

import networkx as nx


def find_top_core(G: nx.Graph) -> set[frozenset] | None:
    """
    Returns the edge set of the minimal core of G (as a set of
    frozenset({u,v})) if one exists (i.e. if some proper subset of
    vertices ties G's own density), or None if G is strictly dense
    (no proper subgraph achieves theta(G)).
    """

    nodes = list(G.nodes())
    n = len(nodes)
    m = G.number_of_edges()
    if n < 3 or m == 0:
        return None

    deg = dict(G.degree())

    # g = m / (n-1); scale all capacities by (n-1) to keep them exact
    # integers: s->v becomes m*(n-1), v->t becomes m*(n+1) - (n-1)*deg(v),
    # each edge arc becomes (n-1).
    #
    # S=V always achieves cut(V) == mn+2g exactly (by construction, since
    # g = theta(G) exactly, and no subgraph can exceed theta(G)'s
    # density under homogeneity). But S=empty *always* achieves a
    # strictly smaller cut (mn, independent of g), so an unconstrained
    # min cut always degenerates to S=empty and reveals nothing. Fixing
    # this requires forcing some vertex to always stay on the source
    # side (via cap(s,v) = infinite, which is the correct direction --
    # NOT cap(v,t), which doesn't prevent v's own s->v edge from being
    # cut). But forcing a SINGLE vertex isn't enough either: singletons
    # are *vacuously* tied under our density (|E({v})| - g*(1-1) = 0 - 0
    # = 0 for every v, since the "-1" makes the constraint disappear for
    # |S|=1), so nx.minimum_cut's own "cannot reach t" side gives the
    # MAXIMAL min-cut (confirmed by inspecting its source: it computes
    # reachability *to* t on the pruned residual graph, not *from* s) --
    # and the true MINIMAL side (which we want, computed by hand via
    # descendants of s in a properly conserved max-flow's residual
    # graph -- NOT preflow_push's value_only=True mode, whose returned
    # "flow" is a preflow with leftover excess near s and so gives a
    # bogus residual graph for this purpose) collapses to a single
    # degenerate vertex instead of the real core.
    #
    # Fix: anchor on an EDGE (force both endpoints of some e0 in G to
    # stay source-side). A forced pair {u0,v0} only has |E|-g*(2-1) =
    # 1-g, which is not a vacuous tie for any g>1 (i.e. any graph with
    # more than n-1 edges), so this can't manufacture a false core --
    # confirmed empirically: anchoring any actual roof edge of the house
    # graph reveals exactly the roof, and anchoring any non-roof edge
    # correctly falls back to S=V. Theorem 8.1 guarantees a unique
    # minimal core when one exists, so trying edges until one reveals a
    # proper subset (or all are exhausted, confirming rigidity) is
    # correct.
    s, t = "__s__", "__t__"
    cap_sv = m * (n - 1)
    big = cap_sv * n * 10 + 1  # larger than any achievable cut value

    # Nested ties are possible (e.g. in the multi-level house family,
    # stacking full levels preserves the same density as the whole
    # graph), so the minimal-S-containing-this-edge result differs by
    # which edge is anchored: an edge inside the true (topmost) minimal
    # core gives back exactly that core, but an edge further out gives
    # back a larger tied superset that also happens to contain the
    # anchor. Confirmed on multi_level_house_graph(2): both the top
    # triangle {4,5,6} and the two-level union {2,3,4,5,6} tie at the
    # same density.
    #
    # Rather than trying every edge and keeping the global smallest
    # (correct but O(m) full flow computations per level -- measured
    # cubic-ish blowup, unusable past a few dozen levels), stop at the
    # FIRST proper subset found and recurse into it: any tied proper
    # subset found this way still ties at exactly the same g (since the
    # subset's own density equals theta(G) by construction), so calling
    # find_top_core again on just that smaller induced subgraph correctly
    # shrinks it further using a far smaller edge set, converging to the
    # same unique minimal core at a fraction of the cost.
    for u0, v0 in G.edges():
        F = nx.DiGraph()
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
        residual = nx.DiGraph()
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
            core_edges = {frozenset((a, b)) for a, b in G.edges()
                          if a in core_vertices and b in core_vertices}
            if core_edges:
                sub = G.subgraph(core_vertices)
                smaller = find_top_core(sub)
                return smaller if smaller is not None else core_edges

    return None


def core_edges_to_vertices(core_edges: set[frozenset]) -> set:
    vs = set()
    for e in core_edges:
        vs |= set(e)
    return vs


def deflation_sequence(G: nx.Graph, verbose: bool = True) -> list[set[frozenset]]:
    cores: list[set[frozenset]] = []
    current = G.copy()
    rep = {v: {v} for v in G.nodes()}

    level = 0
    while True:
        core = find_top_core(current)
        if core is None:
            if verbose:
                print(f"level {level}: no further core -- graph is rigid "
                      f"({current.number_of_nodes()} vertices, {current.number_of_edges()} edges left)")
            break

        core_vertices = core_edges_to_vertices(core)
        orig_edges = set()
        for e in core:
            u, v = tuple(e)
            orig_edges |= {frozenset((ou, ov)) for ou in rep[u] for ov in rep[v]
                            if G.has_edge(ou, ov)}
        cores.append(orig_edges)
        if verbose:
            core_str = sorted((tuple(e) for e in core), key=lambda e: tuple(map(str, e)))
            orig_str = sorted((tuple(e) for e in orig_edges), key=lambda e: tuple(map(str, e)))
            print(f"level {level}: core = {core_str} (original edges: {orig_str})")

        new_point = f"P{level}"
        H = current.copy()
        core_list = list(core_vertices)
        for v in core_list[1:]:
            H = nx.contracted_nodes(H, core_list[0], v, self_loops=False)
        H = nx.relabel_nodes(H, {core_list[0]: new_point})
        current = H
        merged_rep = set()
        for v in core_vertices:
            merged_rep |= rep[v]
        rep = {v: rep[v] for v in current.nodes() if v != new_point}
        rep[new_point] = merged_rep

        level += 1
        if level > 200:
            raise RuntimeError("deflation did not terminate")

    return cores


if __name__ == "__main__":
    import time

    def multi_level_house_graph(levels: int) -> nx.Graph:
        G = nx.Graph()
        for i in range(levels + 1):
            a, b = 2 * i, 2 * i + 1
            G.add_edge(a, b)
            if i > 0:
                G.add_edge(a - 2, a)
                G.add_edge(b - 2, b)
        apex = 2 * (levels + 1)
        top_a, top_b = 2 * levels, 2 * levels + 1
        G.add_edge(top_a, apex)
        G.add_edge(top_b, apex)
        return G

    print("=== diamond graph (expect no core -- strictly homogeneous) ===")
    diamond = nx.Graph([(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)])
    cores = deflation_sequence(diamond)
    print(f"  total cores found: {len(cores)} (expect 0)\n")

    for levels in [1, 2, 3, 4, 5]:
        print(f"=== multi_level_house_graph({levels}) ===")
        G = multi_level_house_graph(levels)
        t0 = time.perf_counter()
        cores = deflation_sequence(G)
        elapsed = time.perf_counter() - t0
        print(f"  total cores found: {len(cores)} (expect {levels}), {elapsed:.3f}s\n")

    print("=== scaling check (no brute-force enumeration involved) ===")
    for levels in [10, 50, 200, 1000]:
        G = multi_level_house_graph(levels)
        t0 = time.perf_counter()
        cores = deflation_sequence(G, verbose=False)
        elapsed = time.perf_counter() - t0
        print(f"  levels={levels}: cores found={len(cores)} (expect {levels}), "
              f"n={G.number_of_nodes()}, {elapsed:.3f}s")
