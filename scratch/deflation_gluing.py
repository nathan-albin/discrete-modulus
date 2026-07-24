"""
Constructive pmf via recursive core deflation + interval-model gluing
(Theorem 8.1(c) of scratch/determinant_paper.pdf).

Uses core_deflation.py to find the sequence of minimal cores (roofs) via
the minimum-determinant optimization's divergence pattern. For the fully
rigid base and each core, gets a small LOCAL exact pmf (via
matroid_union_packing.build_tree_packing at the minimal scale, since
these rigid pieces have no forbidden trees, matching the pattern already
validated on K_n). Then glues everything into one pmf on spanning trees
of the original graph by taking every combination of (base tree, core_1
tree, core_2 tree, ...) independently -- a Cartesian product, weighted by
the product of the local probabilities (the "stacked interval models").

Why this is exact and always valid: each core's edges are edge-disjoint
from the rest of the graph, sharing only attachment (rail) vertices, not
edges -- so combining any independently-valid local tree choices can
never create a cycle. This was checked by hand on several cases before
implementing, and Theorem 8.1(c) guarantees it in general.
"""

from __future__ import annotations

import sys
from fractions import Fraction

import networkx as nx

sys.path.insert(0, "/workspaces/discrete-modulus/scratch")
from core_deflation_maxflow import find_top_core  # noqa: E402
from matroid_union_packing import build_tree_packing  # noqa: E402


def _local_pmf(H: nx.Graph, seed: int = 0) -> list[tuple[frozenset, Fraction]]:
    """
    Exact pmf on spanning trees of a small rigid graph H (no forbidden
    trees expected), as (tree-edge-set, weight) pairs at the minimal
    integer scale matching H's reduced (target/m) fraction.
    """

    n = H.number_of_nodes()
    m = H.number_of_edges()
    target_num, target_den = Fraction(n - 1, m).numerator, Fraction(n - 1, m).denominator
    # minimal scale: m' = target_den, target' = target_num
    for attempt_seed in range(seed, seed + 20):
        result = build_tree_packing(H, m=target_den, target=target_num, seed=attempt_seed,
                                     max_passes=500, verbose=False)
        if result is not None:
            break
    else:
        raise RuntimeError(f"could not find local pmf for rigid piece with {n} vertices, {m} edges")

    weight = Fraction(1, target_den)
    return [(frozenset(frozenset(e) for e in T.edges()), weight) for T in result]


def deflate_with_provenance(G: nx.Graph, verbose: bool = True):
    """
    Like core_deflation.deflation_sequence, but also tracks, for every
    edge at every level, which ORIGINAL edge of G it represents -- so
    cores and the final base can be expressed as small graphs whose own
    edges are labeled with their original-graph identity, ready for
    gluing.

    Returns (cores, base), where cores is a list of (core_graph,
    edge_provenance) from outermost to innermost, edge_provenance maps
    each core_graph edge (as a frozenset of core_graph's own vertices)
    to the corresponding original-graph edge (frozenset of original
    vertices); base is (base_graph, base_provenance) similarly.
    """

    current = G.copy()
    for u, v in G.edges():
        current[u][v]["orig"] = frozenset((u, v))

    cores = []
    level = 0
    while True:
        core_edges_local = find_top_core(current)
        if core_edges_local is None:
            base_provenance = {frozenset((u, v)): current[u][v]["orig"] for u, v in current.edges()}
            if verbose:
                print(f"level {level}: rigid base, {current.number_of_nodes()} vertices, "
                      f"{current.number_of_edges()} edges")
            return cores, (current.copy(), base_provenance)

        core_vertices = set()
        for e in core_edges_local:
            core_vertices |= set(e)

        core_graph = current.subgraph(core_vertices).copy()
        core_provenance = {frozenset((u, v)): current[u][v]["orig"] for u, v in core_graph.edges()}
        cores.append((core_graph, core_provenance))
        if verbose:
            orig = sorted(tuple(sorted(v, key=str)) for v in core_provenance.values())
            print(f"level {level}: core with {core_graph.number_of_nodes()} vertices "
                  f"(original edges: {orig})")

        # contract the core to a single new point, carrying "orig" edge labels outward
        new_point = f"__P{level}__"
        H = nx.Graph()
        H.add_nodes_from(v for v in current.nodes() if v not in core_vertices)
        H.add_node(new_point)
        for u, v, data in current.edges(data=True):
            if u in core_vertices and v in core_vertices:
                continue  # internal core edge, absorbed
            uu = new_point if u in core_vertices else u
            vv = new_point if v in core_vertices else v
            if uu == vv:
                continue
            H.add_edge(uu, vv, orig=data["orig"])

        current = H
        level += 1
        if level > 50:
            raise RuntimeError("deflation did not terminate")


def build_glued_pmf(G: nx.Graph, verbose: bool = True) -> list[tuple[frozenset, Fraction]]:
    cores, (base_graph, base_provenance) = deflate_with_provenance(G, verbose=verbose)

    # local pmf for the base, translated to original-graph edges
    base_local = _local_pmf(base_graph)
    pieces: list[list[tuple[frozenset, Fraction]]] = [
        [(frozenset(base_provenance[e] for e in tree), w) for tree, w in base_local]
    ]

    # local pmf for each core (innermost first doesn't matter here -- each
    # core's own edges translate directly via its own provenance map,
    # independent of the others)
    for core_graph, core_provenance in cores:
        local = _local_pmf(core_graph)
        pieces.append([(frozenset(core_provenance[e] for e in tree), w) for tree, w in local])

    if verbose:
        sizes = [len(p) for p in pieces]
        total = 1
        for s in sizes:
            total *= s
        print(f"gluing {len(pieces)} pieces, local sizes={sizes}, total combined trees={total}")

    # Cartesian product: every combination of one tree per piece
    glued: list[tuple[frozenset, Fraction]] = [(frozenset(), Fraction(1))]
    for piece in pieces:
        new_glued = []
        for acc_edges, acc_w in glued:
            for tree, w in piece:
                new_glued.append((acc_edges | tree, acc_w * w))
        glued = new_glued

    return glued


def verify_glued_pmf(G: nx.Graph, glued: list[tuple[frozenset, Fraction]]) -> bool:
    n = G.number_of_nodes()
    m = G.number_of_edges()
    target = Fraction(n - 1, m)

    total_weight = sum(w for _, w in glued)
    if total_weight != 1:
        print(f"  FAIL: weights sum to {total_weight}, not 1")
        return False

    for tree, w in glued:
        if len(tree) != n - 1:
            print(f"  FAIL: a 'tree' has {len(tree)} edges, expected {n - 1}")
            return False
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        H.add_edges_from(tuple(e) for e in tree)
        if not nx.is_connected(H):
            print("  FAIL: a combined tree is not connected")
            return False

    marginal: dict = {frozenset(e): Fraction(0) for e in G.edges()}
    for tree, w in glued:
        for e in tree:
            marginal[e] += w

    bad = [(e, v) for e, v in marginal.items() if v != target]
    if bad:
        print(f"  FAIL: {len(bad)} edges have wrong marginal (want {target}): {bad[:5]}")
        return False

    return True


if __name__ == "__main__":
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

    for levels in [1, 2, 3]:
        print(f"=== levels={levels} ===")
        G = multi_level_house_graph(levels)
        glued = build_glued_pmf(G)
        ok = verify_glued_pmf(G, glued)
        print(f"  verified: {ok}, support size: {len(glued)}")
        print()
