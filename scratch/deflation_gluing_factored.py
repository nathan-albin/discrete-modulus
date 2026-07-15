"""
Factored ("recipe") representation of the glued pmf, as an alternative to
deflation_gluing.py's explicit flat list.

Instead of materializing the full Cartesian product of the base and every
core's local pmf (support size = product of local sizes, e.g. 3^levels
for the multi-level house family -- intractable past ~10 levels), this
represents the certificate as:

  - the base's local pmf and each core's local pmf, each small
    (independent of how many levels there are -- e.g. always size 3 for
    a triangle piece), plus
  - the pre-image map from each piece's own edges back to the edges of
    the original graph G.

"Picking a spanning tree of G" = independently pick one local tree from
each piece according to its own pmf, then take the union of the
pre-images of the edges collected. Marginals on G are correct because
they're correct on each piece separately, and every edge of G belongs to
exactly one piece (the pieces partition E(G) -- see deflation_gluing.py's
docstring for why cores/base are edge-disjoint).

This is the same underlying product measure as deflation_gluing.py's
explicit version -- just represented compactly. Validating it here can't
rely on exhaustively summing over the full support (that's the whole
point), so instead: (a) check each local piece's own pmf is exact and
correct on its own edges, (b) check the pieces partition E(G) exactly
(no edge in two pieces, no edge left out), and (c) statistically sample
many glued trees and confirm each one is a genuine spanning tree of G
(structural spot-check; exact marginals already follow from (a)+(b) by
construction, not from sampling).
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction

import networkx as nx

sys.path.insert(0, "/workspaces/discrete-modulus/scratch")
from deflation_gluing import _local_pmf, deflate_with_provenance  # noqa: E402  (now backed by core_deflation_maxflow)


class FactoredPmf:
    """
    pieces: list of (local_pmf, provenance), one per piece (base first,
    then each core). local_pmf is a list of (local-tree-edge-set,
    Fraction weight); provenance maps a piece's own edge (frozenset of
    the piece's own vertices) to the corresponding edge of the original
    graph G (frozenset of G's vertices).
    """

    def __init__(self, pieces: list[tuple[list[tuple[frozenset, Fraction]], dict]]):
        self.pieces = pieces

    def sample(self, rng: random.Random) -> frozenset:
        """Independently sample a local tree from each piece, glue via pre-images."""
        result: set = set()
        for local_pmf, provenance in self.pieces:
            trees, weights = zip(*local_pmf)
            tree = rng.choices(trees, weights=[float(w) for w in weights], k=1)[0]
            for e in tree:
                result.add(provenance[e])
        return frozenset(result)

    def check_partition(self, G: nx.Graph) -> bool:
        """Every edge of G must appear in the range of exactly one piece's provenance."""
        seen: dict = {}
        ok = True
        for pi, (_, provenance) in enumerate(self.pieces):
            for orig_edge in provenance.values():
                if orig_edge in seen:
                    print(f"  FAIL: edge {tuple(orig_edge)} claimed by both piece {seen[orig_edge]} "
                          f"and piece {pi}")
                    ok = False
                seen[orig_edge] = pi
        g_edges = {frozenset(e) for e in G.edges()}
        missing = g_edges - set(seen.keys())
        extra = set(seen.keys()) - g_edges
        if missing:
            print(f"  FAIL: {len(missing)} edges of G not covered by any piece: {list(missing)[:5]}")
            ok = False
        if extra:
            print(f"  FAIL: {len(extra)} piece edges don't correspond to a real G edge")
            ok = False
        return ok

    def check_local_pmfs_exact(self) -> bool:
        ok = True
        for pi, (local_pmf, _) in enumerate(self.pieces):
            total = sum(w for _, w in local_pmf)
            if total != 1:
                print(f"  FAIL: piece {pi}'s local weights sum to {total}, not 1")
                ok = False
            marginal: dict = {}
            for tree, w in local_pmf:
                for e in tree:
                    marginal[e] = marginal.get(e, Fraction(0)) + w
            vals = set(marginal.values())
            if len(vals) != 1:
                print(f"  FAIL: piece {pi}'s local marginals aren't uniform: {vals}")
                ok = False
        return ok


def build_factored_pmf(G: nx.Graph, verbose: bool = True) -> FactoredPmf:
    cores, (base_graph, base_provenance) = deflate_with_provenance(G, verbose=verbose)

    pieces = [(_local_pmf(base_graph), base_provenance)]
    for core_graph, core_provenance in cores:
        pieces.append((_local_pmf(core_graph), core_provenance))

    return FactoredPmf(pieces)


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

    import time

    for levels in [5, 10, 20, 50]:
        G = multi_level_house_graph(levels)
        t0 = time.perf_counter()
        pmf = build_factored_pmf(G, verbose=False)
        elapsed = time.perf_counter() - t0

        part_ok = pmf.check_partition(G)
        local_ok = pmf.check_local_pmfs_exact()

        rng = random.Random(0)
        n_samples = 200
        all_valid = True
        for _ in range(n_samples):
            tree = pmf.sample(rng)
            if len(tree) != G.number_of_nodes() - 1:
                all_valid = False
                break
            H = nx.Graph()
            H.add_nodes_from(G.nodes())
            H.add_edges_from(tuple(e) for e in tree)
            if not nx.is_connected(H):
                all_valid = False
                break

        total_local_size = sum(len(p[0]) for p in pmf.pieces)
        print(f"levels={levels}: build={elapsed:.3f}s, pieces={len(pmf.pieces)}, "
              f"total local pmf size={total_local_size} (vs {3**(levels+1)} for the flat product), "
              f"partition_ok={part_ok}, local_pmfs_ok={local_ok}, "
              f"{n_samples} sampled trees all valid={all_valid}")
