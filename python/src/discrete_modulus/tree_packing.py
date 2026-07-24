"""
Constructive integer spanning-tree packing: an alternative to
`min_norm_point.min_norm_point_wolfe` for building the exact uniform
local pmf on a strictly homogeneous piece (`core_deflation`'s rigid
base or any core -- see `pmf_construction`).

Motivation: every piece `pmf_construction.build_factored_pmf` ever
hands a solver is strictly homogeneous with a single uniform theta --
not a general target marginal, which is the case `min_norm_point_wolfe`
is built for. Given theta = p/q in lowest terms, this module instead
builds q spanning trees directly, such that every edge (each parallel
copy counted separately) is used in exactly p of them; weighting each
tree 1/q gives the (unique, by strict homogeneity) uniform pmf -- no
continuous optimization at all.

Once a certificate is built it lasts forever, so raw speed matters far
less than not having a long, unpredictable tail -- which is exactly
Wolfe's failure mode on some pieces: its active set can grow for
minutes with no sign of convergence, purely from vertex/edge-labeling
sensitivity, with no cheap way to predict which pieces will do this in
advance. This module's cost is bounded instead by q (the piece's own
theta denominator) times a handful of MST calls, and was validated on:
the real piece that caused Wolfe's long tail (`examples/nested`'s
round-2 K20-shaped piece), the two complete-graph sizes (K40/K50) that
stalled single-hop swaps alone, and several genuinely sparse,
non-complete homogeneous pieces obtained by peeling random sparse graphs
down to a rigid base via `core_deflation`.

Two-tier method:

1. Away-step (`_away_step_pass`): repeatedly evict the heaviest tree
   (by total coverage-weight of its own edges) and replace it with the
   tree that *provably* minimizes the resulting energy
   E(w) = sum_e (w(e)-p)^2, among ALL possible replacements -- one MST
   call, using edge weights derived from the current coverage
   deficiency. Every spanning tree has the same edge count, so
   sum_e w(e) is invariant under any tree-for-tree replacement --
   minimizing E(w) is therefore equivalent to minimizing sum_e w(e)^2.
   Writing d(e) = w(e)-p and removing the chosen tree T_h first, the
   coverage becomes w(e) - 1_{e in T_h}, and for any candidate
   replacement tree T:

       E(w') = const(T_h-independent) + 2 * sum_{e in T} d'(e)

   where d'(e) = d(e) - 1_{e in T_h}(e). So the T that minimizes E(w')
   is exactly the MINIMUM d'-weight spanning tree. Since T_h itself is
   a valid candidate, this move is guaranteed non-increasing. Ties are
   broken, in exact integer arithmetic, in favor of the tree least
   overlapping T_h (scale d' by 2q+1 and add 1 for edges in T_h) --
   without this, swapping to an equally-good-but-different tree can
   silently make zero progress. Even with tie-breaking this is not by
   itself a complete algorithm: it can reach a genuine local minimum
   (T_h already IS its own energy-minimizing replacement) before E
   hits 0.
2. BFS multi-hop augmenting search (`_find_augmenting_chain`), the
   fallback whenever (1) stalls: build the matroid exchange graph on
   edges (x -> y via tree T_i whenever T_i - x + y is still a valid
   spanning tree) and BFS from all over-covered edges simultaneously to
   any under-covered edge, restricted to using each tree at most once
   along a given path (each tree's own exchange is independently valid
   in its pre-chain state, so applying a whole path's exchanges
   together can't conflict within any one tree).
"""

from __future__ import annotations

import random
from collections import deque
from fractions import Fraction

import networkx as nx
import numpy as np

from .families.networkx_families import MinimumSpanningTree
from .protocols import MinNormPointResult, SupportEntry


def _tree_graph(G: nx.Graph, cons: list) -> nx.Graph:
    Tg: nx.Graph = nx.MultiGraph() if G.is_multigraph() else nx.Graph()
    Tg.add_nodes_from(G.nodes())
    if G.is_multigraph():
        for u, v, k in cons:
            Tg.add_edge(u, v, key=k)
    else:
        Tg.add_edges_from(cons)
    return Tg


def _energy(coverage: np.ndarray, target: int) -> int:
    return int(np.sum((coverage - target) ** 2))


def _away_step_pass(
    G: nx.Graph,
    finder: MinimumSpanningTree,
    q: int,
    target: int,
    trees: list[np.ndarray],
    tree_graphs: list[nx.Graph],
    coverage: np.ndarray,
) -> bool:
    """One away-step move; see the module docstring. Returns True iff
    the energy strictly decreased."""

    E_before = _energy(coverage, target)
    if E_before == 0:
        return False

    totals = [int(np.dot(coverage, trees[i])) for i in range(q)]
    h = max(range(q), key=lambda i: totals[i])
    h_usage = trees[h]

    scale = 2 * q + 1
    dprime = coverage - target - h_usage
    weights = scale * dprime + h_usage

    result = finder(weights, 0.0)
    assert result.n is not None
    new_usage = result.n.astype(np.int64)

    coverage += new_usage - h_usage
    trees[h] = new_usage
    tree_graphs[h] = _tree_graph(G, result.cons)

    return _energy(coverage, target) < E_before


def _find_augmenting_chain(
    G: nx.Graph,
    m: int,
    q: int,
    target: int,
    trees: list[np.ndarray],
    tree_graphs: list[nx.Graph],
    coverage: np.ndarray,
    edge_list: list,
) -> list[tuple[int, int, int]] | None:
    """BFS for a multi-hop augmenting chain; see the module docstring.
    Returns a list of (tree_index, x_edge, y_edge) steps -- edge
    indices into `edge_list`/`coverage` -- to apply in order, or None
    if none exists."""

    over = [e for e in range(m) if coverage[e] > target]
    under_set = {e for e in range(m) if coverage[e] < target}
    if not under_set:
        return []

    visited: dict[int, tuple | None] = {}
    used_trees_at: dict[int, frozenset] = {}
    queue: deque = deque()
    for x0 in over:
        if x0 not in visited:
            visited[x0] = None
            used_trees_at[x0] = frozenset()
            queue.append(x0)

    target_edge = None
    while queue:
        x = queue.popleft()
        if x in under_set:
            target_edge = x
            break

        used_here = used_trees_at[x]
        xu, xv = edge_list[x][0], edge_list[x][1]
        for i in range(q):
            if i in used_here or not trees[i][x]:
                continue

            Tg = tree_graphs[i]
            if G.is_multigraph():
                xk = edge_list[x][2]
                Tg.remove_edge(xu, xv, xk)  # type: ignore[call-arg]
            else:
                Tg.remove_edge(xu, xv)
            comp = set(nx.node_connected_component(Tg, xu))
            if G.is_multigraph():
                Tg.add_edge(xu, xv, key=xk)
            else:
                Tg.add_edge(xu, xv)

            for y in range(m):
                if trees[i][y] or y in visited:
                    continue
                yu, yv = edge_list[y][0], edge_list[y][1]
                if (yu in comp) != (yv in comp):
                    visited[y] = (x, i)
                    used_trees_at[y] = used_here | {i}
                    queue.append(y)

    if target_edge is None:
        return None

    chain: list[tuple[int, int, int]] = []
    y = target_edge
    while True:
        entry = visited[y]
        if entry is None:
            break
        x, i = entry
        chain.append((i, x, y))
        y = x
    chain.reverse()
    return chain


def _apply_chain(
    chain: list[tuple[int, int, int]],
    G: nx.Graph,
    edge_list: list,
    trees: list[np.ndarray],
    tree_graphs: list[nx.Graph],
    coverage: np.ndarray,
) -> None:
    for i, x, y in chain:
        xu, xv = edge_list[x][0], edge_list[x][1]
        yu, yv = edge_list[y][0], edge_list[y][1]
        Tg = tree_graphs[i]
        if G.is_multigraph():
            Tg.remove_edge(xu, xv, edge_list[x][2])  # type: ignore[call-arg]
            Tg.add_edge(yu, yv, key=edge_list[y][2])
        else:
            Tg.remove_edge(xu, xv)
            Tg.add_edge(yu, yv)
        trees[i][x] = 0
        trees[i][y] = 1
        coverage[x] -= 1
        coverage[y] += 1


def build_tree_packing(
    G: nx.Graph,
    p: int,
    q: int,
    max_away_iters: int = 2000,
    max_augment_rounds: int = 2000,
    seed: int = 0,
    max_restarts: int = 50,
) -> MinNormPointResult | None:
    """
    Builds the exact uniform pmf on spanning trees of a strictly
    homogeneous (multi)graph `G` whose theta is `p/q` (lowest terms):
    `q` spanning trees, each edge used in exactly `p` of them, each
    tree weighted `1/q`. See the module docstring for the algorithm.

    Retries with a fresh random initialization (up to `max_restarts`
    times) whenever one attempt's BFS augmenting search reports no
    chain exists from its current state. This isn't a completeness gap
    worth chasing further here: the restriction that makes the BFS
    chain search cheap to verify correct (each tree used at most once
    per chain) is a sufficient but not obviously necessary condition,
    so a "stuck" report means this particular restricted search found
    no chain, not that none exists nor that the configuration is
    unsalvageable -- a fresh random start reliably escapes it in
    practice. Empirically, on the tightest case found so far (a 21
    vertex/40 edge piece needing an exact 2-tree edge partition, theta =
    1/2 -- no slack at all, the hardest kind of instance for this
    method), roughly 1 in 3 random restarts succeeds outright, so
    `max_restarts=50` drives the overall failure probability well below
    1e-8. Since a certificate is built once and lasts forever, paying
    for a few dozen cheap attempts is a good trade for not needing a
    fully complete (and considerably more involved) matroid-union
    implementation.

    Returns
    -------
    MinNormPointResult, or None if every restart's packing search
    failed to converge within the iteration budgets.
    """

    for attempt in range(max_restarts):
        result = _attempt_packing(G, p, q, max_away_iters, max_augment_rounds, seed=seed + attempt)
        if result is not None:
            return result
    return None


def _attempt_packing(
    G: nx.Graph,
    p: int,
    q: int,
    max_away_iters: int,
    max_augment_rounds: int,
    seed: int,
) -> MinNormPointResult | None:
    finder = MinimumSpanningTree(G)
    m = G.number_of_edges()

    edge_list: list[tuple]
    if G.is_multigraph():
        edge_list = [(u, v, k) for u, v, k in G.edges(keys=True)]  # type: ignore[call-overload]
    else:
        edge_list = [(u, v) for u, v in G.edges()]

    rng = random.Random(seed)
    trees: list[np.ndarray] = []
    tree_graphs: list[nx.Graph] = []
    coverage = np.zeros(m, dtype=np.int64)
    for _ in range(q):
        rho = np.array([rng.random() for _ in range(m)])
        result = finder(rho, 0.0)
        assert result.n is not None
        usage = result.n.astype(np.int64)
        trees.append(usage)
        tree_graphs.append(_tree_graph(G, result.cons))
        coverage += usage

    away_iters = 0
    for it in range(max_away_iters):
        away_iters = it
        if _energy(coverage, p) == 0:
            break
        if not _away_step_pass(G, finder, q, p, trees, tree_graphs, coverage):
            break

    augment_rounds = 0
    for it in range(max_augment_rounds):
        augment_rounds = it
        if _energy(coverage, p) == 0:
            break
        chain = _find_augmenting_chain(G, m, q, p, trees, tree_graphs, coverage, edge_list)
        if chain is None:
            return None
        _apply_chain(chain, G, edge_list, trees, tree_graphs, coverage)
        _away_step_pass(G, finder, q, p, trees, tree_graphs, coverage)

    if _energy(coverage, p) != 0:
        return None

    weight = Fraction(1, q)
    support = [
        SupportEntry(
            cons=[edge_list[e] for e in range(m) if trees[i][e]],
            n=np.array([Fraction(int(v)) for v in trees[i]], dtype=object),
            weight=weight,
        )
        for i in range(q)
    ]
    x = np.array([Fraction(p, q)] * m, dtype=object)
    return MinNormPointResult(
        x=x,
        support=support,
        iterations=away_iters,
        oracle_calls=q + away_iters + augment_rounds,
        extra_stats={"augment_rounds": augment_rounds},
    )
