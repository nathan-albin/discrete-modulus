"""
Open validation task from Certification_Plan.md Sec 5.1: run
`min_norm_point_wolfe` against a real multi-round shrunk graph, now that
PR 1's solver-trace instrumentation exists to produce one.

`examples/nested` decomposes into 3 rounds (theta = 1/2, 1/4, 1/10; crit_set
sizes 40/80/190). For each round, the "shrunk multigraph" G~ = (V~, C) that
Sec 5.1's setup describes is *not* directly in the trace -- the trace only
records the round's raw component vertex set and crit_set (per PR 1's
deliberately minimal scope). But it doesn't need to be: since pieces only
ever separate (never re-merge) as spanning_tree_modulus recurses, round k's
component h_k is exactly the ORIGINAL graph induced on that round's recorded
vertex set -- no need for the trace to carry h_k's full edge list or any
earlier round's crit_set. So:

  h_k          = g.subgraph(round_k.vertices)
  pieces       = connected_components(h_k - round_k.crit_set)
  G~ (round k) = pieces, contracted, with round_k.crit_set as edges

This was confirmed computationally against the trace before writing this
script (see conversation) -- round 0 has 60 raw vertices contracting to 21
pieces, round 1 has 40 contracting to 21, round 2 (=K20, already covered by
the existing K_n sweep) has 20 contracting to 20 (no contraction at all).
Round 1's G~ has genuine parallel edges (max multiplicity 3), so this uses a
small MultiGraph-aware oracle rather than `MinimumSpanningTree`, which
assumes a simple `nx.Graph` (see its `__init__`: `G[u][v]["enum"] = i` isn't
multigraph-safe).
"""

from __future__ import annotations

import json
import shutil
import subprocess
import time
from fractions import Fraction

import networkx as nx
import numpy as np

from discrete_modulus.min_norm_point import min_norm_point_wolfe
from discrete_modulus.protocols import ExactArray, ShortestResult

REPO = "/workspaces/discrete-modulus"


class MultigraphMinimumSpanningTree:
    """Like `families.networkx_families.MinimumSpanningTree`, but safe for
    an `nx.MultiGraph` with parallel edges."""

    def __init__(self, G: nx.MultiGraph) -> None:
        self.G = G
        self.edges = list(G.edges(keys=True))
        self.enum = {(frozenset((u, v)), k): i for i, (u, v, k) in enumerate(self.edges)}

    def __call__(self, rho, tol: float) -> ShortestResult:
        for i, (u, v, k) in enumerate(self.edges):
            self.G[u][v][k]["rho"] = rho[i]

        T = list(nx.minimum_spanning_edges(self.G, weight="rho", data=False, keys=True))

        n: ExactArray = np.array([Fraction(0)] * len(self.edges), dtype=object)
        for u, v, k in T:
            n[self.enum[(frozenset((u, v)), k)]] = Fraction(1)
        return ShortestResult(T, n)


def load_edges(path: str) -> nx.Graph:
    g = nx.Graph()
    with open(path) as f:
        n = int(f.readline())
        g.add_nodes_from(range(n))
        for line in f:
            u, v = map(int, line.split())
            g.add_edge(u, v)
    return g


def build_shrunk_multigraph(g: nx.Graph, vertices: list[int], crit_set: list[tuple[int, int]]) -> nx.MultiGraph:
    h = g.subgraph(vertices).copy()
    h_minus_crit = h.copy()
    h_minus_crit.remove_edges_from(crit_set)

    piece_of: dict[int, int] = {}
    for idx, piece in enumerate(nx.connected_components(h_minus_crit)):
        for v in piece:
            piece_of[v] = idx

    shrunk = nx.MultiGraph()
    shrunk.add_nodes_from(range(len(set(piece_of.values()))))
    for u, v in crit_set:
        shrunk.add_edge(piece_of[u], piece_of[v])
    return shrunk


def validate_round(index: int, g: nx.Graph, round_data: dict) -> None:
    vertices = round_data["vertices"]
    crit_set = [tuple(e) for e in round_data["crit_set"]]
    theta = Fraction(*round_data["theta"])

    shrunk = build_shrunk_multigraph(g, vertices, crit_set)
    n_pieces = shrunk.number_of_nodes()
    m = shrunk.number_of_edges()
    max_mult = max((shrunk.number_of_edges(u, v) for u, v in {(u, v) for u, v, _ in shrunk.edges(keys=True)}), default=0)

    print(f"\n--- round {index}: theta={theta}, pieces={n_pieces}, |C|={m}, max parallel multiplicity={max_mult} ---")

    oracle = MultigraphMinimumSpanningTree(shrunk)
    t0 = time.perf_counter()
    result = min_norm_point_wolfe(m, oracle)
    elapsed = time.perf_counter() - t0

    # marginals: sum of support weight on every edge should equal theta exactly
    marginal = [Fraction(0)] * m
    for entry in result.support:
        for i, v in enumerate(entry.n):
            marginal[i] += entry.weight * v
    assert all(v == theta for v in marginal), "marginal mismatch!"
    assert sum(e.weight for e in result.support) == 1, "weights don't sum to 1!"

    print(f"  converged: {elapsed:.3f}s, {result.iterations} major, "
          f"{result.extra_stats['minor_iterations']} minor, "
          f"{result.extra_stats['active_set_removals']} evictions, "
          f"{result.oracle_calls} oracle calls")
    print(f"  support size: {len(result.support)} (Caratheodory bound: {n_pieces})")
    print("  marginals: all exactly theta -- OK")


def main() -> None:
    g = load_edges(f"{REPO}/cpp/examples/nested.edges")

    shutil.copy(f"{REPO}/cpp/examples/nested.edges", "/tmp/nested_validation.edges")
    subprocess.run([f"{REPO}/cpp/build/spt_mod", "/tmp/nested_validation", "--trace"],
                    check=True, stdout=subprocess.DEVNULL)
    with open("/tmp/nested_validation.trace.json") as f:
        trace = json.load(f)

    for i, round_data in enumerate(trace["rounds"]):
        validate_round(i, g, round_data)


if __name__ == "__main__":
    main()
