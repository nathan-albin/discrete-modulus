"""
Recursive core detection via the minimum-determinant optimization from
scratch/determinant_paper.pdf (Albin, Lind, Melikyan, Poggi-Corradini,
"Minimizing the Determinant of the Graph Laplacian"), applied to find the
"minimal core" (Theorem 8.1) of a homogeneous-but-not-strictly-homogeneous
graph -- the "roof" in conversation's house-graph language.

Mechanism (Example 1.4/1.18 in the paper, confirmed numerically in
conversation): minimize log(sum_gamma exp(usage(gamma) . r)) over edge
log-weights r subject to sum(r)=0. If the graph is strictly homogeneous, a
finite minimizer exists (every r settles to a finite value). If not
(house graph and up), the minimizing SEQUENCE has some edges' weights
diverge to +inf while others diverge to -inf -- the induced subgraph on
the diverging-positive edges is exactly the minimal core (Theorem 8.1).
Comparing solutions at two different optimizer precisions separates
edges that are still genuinely diverging from edges that have already
settled to a finite limit (needed because SLSQP reports "converged" once
the objective stops improving much, even while parameters keep drifting
along an unbounded ray).

Once the top core is found, contract it to a point and recurse on the
resulting (smaller) graph -- Theorem 8.1's deflation process -- until a
graph is reached with no divergence at all (a "strictly dense" / fully
rigid graph, with no forbidden trees).
"""

from __future__ import annotations

import networkx as nx
import numpy as np
from scipy.optimize import minimize


def _solve_min_determinant(G: nx.Graph, ftol: float) -> tuple[list[tuple], np.ndarray]:
    """
    Minimizes log(sum_gamma sigma[gamma]) = log(det'(L_sigma)) - log(|V|)
    over edge log-weights r (sigma(e) = exp(r(e))), subject to sum(r)=0.
    Uses Kirchhoff's Matrix Tree Theorem (det'(L_sigma) = |V| * sum_gamma
    sigma[gamma], paper Theorem 1.1) to evaluate the objective via a
    Laplacian determinant, and formula (9) (edge usage probability =
    sigma(e) * effective resistance) for the gradient -- both O(n^3) per
    evaluation via one pseudo-inverse, regardless of how many spanning
    trees the graph has. This replaces an earlier brute-force version
    that enumerated all spanning trees directly and could not scale past
    small graphs.
    """

    nodes = list(G.nodes())
    n = len(nodes)
    node_idx = {v: i for i, v in enumerate(nodes)}
    edges = list(G.edges())
    m = len(edges)
    us = np.array([node_idx[u] for u, v in edges])
    vs = np.array([node_idx[v] for u, v in edges])

    def laplacian(sigma):
        L = np.zeros((n, n))
        for k in range(m):
            i, j = us[k], vs[k]
            L[i, i] += sigma[k]
            L[j, j] += sigma[k]
            L[i, j] -= sigma[k]
            L[j, i] -= sigma[k]
        return L

    def obj(r):
        sigma = np.exp(r)
        L = laplacian(sigma)
        M = L + np.ones((n, n)) / n
        _, logdet = np.linalg.slogdet(M)
        return logdet

    def grad(r):
        sigma = np.exp(r)
        L = laplacian(sigma)
        Lpinv = np.linalg.pinv(L)
        d = np.diag(Lpinv)
        # effR(u,v) = Lpinv[u,u] + Lpinv[v,v] - 2*Lpinv[u,v]
        effR = d[us] + d[vs] - 2 * Lpinv[us, vs]
        return sigma * effR

    cons = {"type": "eq", "fun": lambda r: np.sum(r), "jac": lambda r: np.ones(m)}
    res = minimize(obj, np.zeros(m), jac=grad, constraints=[cons], method="SLSQP",
                    options={"maxiter": 20000, "ftol": ftol})
    return edges, res.x


def find_top_core(G: nx.Graph, diverge_gap: float = 1.0) -> set[frozenset] | None:
    """
    Returns the edge set of the top (most positively diverging) core of
    G, as a set of frozenset({u,v}), or None if G appears strictly dense
    (no divergence detected -- every edge's weight is stable).

    Verified against Example 1.3/1.17's diamond graph (a closed-form,
    finite minimizer): the optimizer's r matches the paper's a* =
    (2/3)^(1/5) exactly, confirming the objective/gradient themselves are
    correct. Divergence is detected the same way as the original
    brute-force version: compare unconstrained solves at two ftol
    levels and see which edges kept drifting under the tighter one
    (a bounded/pinned-at-boundary approach was tried and didn't work --
    SLSQP's ftol stopping criterion kicks in well before r reaches the
    bound, making the bound irrelevant).
    """

    edges, r_loose = _solve_min_determinant(G, ftol=1e-10)
    _, r_tight = _solve_min_determinant(G, ftol=1e-16)

    drift = np.abs(r_tight - r_loose)
    diverging = drift > 1e-3

    if not diverging.any():
        return None

    # among diverging edges, the core is the *positively* diverging cluster
    div_idx = np.where(diverging)[0]
    div_r = r_tight[div_idx]
    order = np.argsort(-div_r)
    sorted_r = div_r[order]

    gaps = sorted_r[:-1] - sorted_r[1:]
    if len(gaps) == 0:
        cut = 1
    else:
        cut = int(np.argmax(gaps)) + 1 if gaps.max() > diverge_gap else len(sorted_r)

    top_idx = div_idx[order[:cut]]
    return {frozenset(edges[i]) for i in top_idx}


def core_edges_to_vertices(core_edges: set[frozenset]) -> set:
    vs = set()
    for e in core_edges:
        vs |= set(e)
    return vs


def deflation_sequence(G: nx.Graph, verbose: bool = True) -> list[set[frozenset]]:
    """
    Returns the sequence of cores (each a set of frozenset edges, in the
    ORIGINAL graph's vertex labels) found by repeatedly detecting the top
    core and contracting it, until no further divergence is found.
    """

    cores: list[set[frozenset]] = []
    current = G.copy()
    # map from current-graph vertex -> set of original vertices it represents
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
        # translate back to original-graph edges for reporting
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

        # contract the core to a single new point
        new_point = f"P{level}"
        merged_rep = set()
        for v in core_vertices:
            merged_rep |= rep[v]
        next_graph = nx.contracted_nodes(current, *core_vertices, self_loops=False, copy=True) \
            if len(core_vertices) == 1 else None
        # networkx doesn't contract >2 nodes in one call cleanly; do it manually
        H = current.copy()
        core_list = list(core_vertices)
        for v in core_list[1:]:
            H = nx.contracted_nodes(H, core_list[0], v, self_loops=False)
        H = nx.relabel_nodes(H, {core_list[0]: new_point})
        current = H
        rep = {v: rep[v] for v in current.nodes() if v != new_point}
        rep[new_point] = merged_rep

        level += 1
        if level > 50:
            raise RuntimeError("deflation did not terminate")

    return cores


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

    for levels in [1, 2, 3, 4]:
        print(f"=== multi_level_house_graph({levels}) ===")
        G = multi_level_house_graph(levels)
        cores = deflation_sequence(G)
        print(f"  total cores found: {len(cores)} (expect {levels})")
        print()
