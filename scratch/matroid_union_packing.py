"""
Prototype: constructive integer spanning-tree packing via matroid exchange
(the "matroid union" approach flagged in Certification_Plan.md Sec 5.1's
IDP action item, and discussed in conversation as a follow-up to
Cunningham's algorithm's tight-set machinery).

Goal: given G~ = (V~, C) with the uniform vector theta*1_C = (n-1)/m * 1_C
known (by construction, from the solver's own tight-set proof) to lie in
the spanning-tree polytope, construct an EXPLICIT multiset of m spanning
trees T_1..T_m such that every edge of C is covered exactly (n-1) times.

Two-tier method:
1. Fast single-hop exchange passes (see `_single_hop_pass`): while some
   edge e* is under-covered and some f* over-covered, look for a tree
   T_i not containing e* whose fundamental cycle (T_i + e*) contains an
   over-covered edge f*; swap. Cheap, handles the bulk of the imbalance
   in practice (verified: K20/K30 fully solved by this alone), but is
   NOT a complete algorithm -- it stalled on K40/K50 with a small residual
   imbalance (2 and 6 respectively, out of tens of thousands), which is
   exactly the classical signature of needing genuine multi-hop augmenting
   chains rather than single direct swaps.
2. BFS multi-hop augmenting search (see `find_augmenting_chain`), the
   fallback when (1) stalls: build the matroid exchange graph on edges
   (x -> y via tree T_i whenever T_i - x + y is still a valid spanning
   tree) and BFS from all over-covered edges simultaneously to any
   under-covered edge, restricted to using each tree at most once along
   a given path (a sufficient, easily-verified-correct condition -- each
   tree's own exchange is independently valid in its pre-chain state, so
   applying all of a path's exchanges together can't conflict within any
   one tree). Applying the resulting chain moves coverage off the source
   (over-covered) edge and onto the sink (under-covered) edge with zero
   net change to every edge in between, by construction.
"""

from __future__ import annotations

import random
import time
from collections import Counter, deque

import networkx as nx


def _norm(e: tuple) -> frozenset:
    return frozenset(e)


def _init_trees(G: nx.Graph, m: int, seed: int) -> tuple[list[nx.Graph], list[set]]:
    edges = list(G.edges())
    rng = random.Random(seed)
    trees: list[nx.Graph] = []
    tree_edge_sets: list[set] = []
    for _ in range(m):
        weights = {e: rng.random() for e in edges}
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        H.add_weighted_edges_from((u, v, weights[(u, v)]) for u, v in edges)
        mst_edges = list(nx.minimum_spanning_edges(H, weight="weight", data=False))
        Tg = nx.Graph()
        Tg.add_nodes_from(G.nodes())
        Tg.add_edges_from(mst_edges)
        trees.append(Tg)
        tree_edge_sets.append({_norm(e) for e in mst_edges})
    return trees, tree_edge_sets


def _single_hop_pass(
    edges: list[tuple], trees: list[nx.Graph], tree_edge_sets: list[set], coverage: Counter, target: int
) -> bool:
    """One pass of single-hop exchanges. Returns True if any progress was made."""

    under = [e for e in edges if coverage[_norm(e)] < target]
    progress = False

    for e_star in under:
        e_star_n = _norm(e_star)
        if coverage[e_star_n] >= target:
            continue

        for Tg, eset in zip(trees, tree_edge_sets):
            if e_star_n in eset:
                continue

            u, v = e_star
            path = nx.shortest_path(Tg, u, v)
            cycle_edges = list(zip(path, path[1:]))

            found = False
            for f in cycle_edges:
                f_n = _norm(f)
                if coverage[f_n] > target:
                    Tg.remove_edge(*f)
                    Tg.add_edge(*e_star)
                    eset.discard(f_n)
                    eset.add(e_star_n)
                    coverage[f_n] -= 1
                    coverage[e_star_n] += 1
                    found = True
                    progress = True
                    break
            if found:
                break

    return progress


def find_augmenting_chain(
    edges: list[tuple], trees: list[nx.Graph], tree_edge_sets: list[set], coverage: Counter, target: int
) -> list[tuple[int, frozenset, frozenset]] | None:
    """
    BFS for a multi-hop augmenting chain from some over-covered edge to
    some under-covered edge. Returns a list of (tree_index, x_removed,
    y_added) steps to apply in order, or None if none exists.
    """

    edge_norms = [_norm(e) for e in edges]
    over = [e for e in edge_norms if coverage[e] > target]
    under_set = {e for e in edge_norms if coverage[e] < target}
    if not under_set:
        return []

    visited: dict[frozenset, tuple | None] = {}
    used_trees_at: dict[frozenset, frozenset] = {}
    queue: deque = deque()
    for f0 in over:
        if f0 not in visited:
            visited[f0] = None
            used_trees_at[f0] = frozenset()
            queue.append(f0)

    target_edge = None
    while queue:
        x = queue.popleft()
        if x in under_set:
            target_edge = x
            break

        used_here = used_trees_at[x]
        xu, xv = tuple(x)
        for i, (Tg, eset) in enumerate(zip(trees, tree_edge_sets)):
            if i in used_here or x not in eset:
                continue

            Tg.remove_edge(xu, xv)
            comp = set(nx.node_connected_component(Tg, xu))
            Tg.add_edge(xu, xv)

            for y in edge_norms:
                if y in eset or y in visited:
                    continue
                yu, yv = tuple(y)
                if (yu in comp) != (yv in comp):
                    visited[y] = (x, i)
                    used_trees_at[y] = used_here | {i}
                    queue.append(y)

    if target_edge is None:
        return None

    chain: list[tuple[int, frozenset, frozenset]] = []
    y = target_edge
    while visited[y] is not None:
        x, i = visited[y]
        chain.append((i, x, y))
        y = x
    chain.reverse()
    return chain


def _apply_chain(
    chain: list[tuple[int, frozenset, frozenset]],
    trees: list[nx.Graph],
    tree_edge_sets: list[set],
    coverage: Counter,
) -> None:
    for i, x, y in chain:
        xu, xv = tuple(x)
        yu, yv = tuple(y)
        trees[i].remove_edge(xu, xv)
        trees[i].add_edge(yu, yv)
        tree_edge_sets[i].discard(x)
        tree_edge_sets[i].add(y)
        coverage[x] -= 1
        coverage[y] += 1


def build_tree_packing(
    G: nx.Graph,
    m: int,
    target: int,
    max_passes: int = 2000,
    max_augment_rounds: int = 2000,
    seed: int = 0,
    verbose: bool = True,
) -> list[nx.Graph] | None:
    edges = list(G.edges())
    trees, tree_edge_sets = _init_trees(G, m, seed)

    coverage: Counter = Counter()
    for eset in tree_edge_sets:
        for e in eset:
            coverage[e] += 1
    for e in edges:
        coverage.setdefault(_norm(e), 0)

    total_passes = 0
    for passnum in range(max_passes):
        total_passes = passnum
        under = [e for e in edges if coverage[_norm(e)] < target]
        if not under:
            if verbose:
                print(f"balanced by single-hop passes alone after {passnum} passes")
            return trees
        if not _single_hop_pass(edges, trees, tree_edge_sets, coverage, target):
            break

    imbalance = sum(abs(coverage[_norm(e)] - target) for e in edges)
    if verbose:
        print(f"single-hop passes stalled after {total_passes} passes, imbalance={imbalance}; "
              f"switching to multi-hop augmenting search")

    for augment_round in range(max_augment_rounds):
        under = [e for e in edges if coverage[_norm(e)] < target]
        if not under:
            if verbose:
                print(f"balanced after {augment_round} augmenting chains")
            return trees

        chain = find_augmenting_chain(edges, trees, tree_edge_sets, coverage, target)
        if chain is None:
            if verbose:
                imbalance = sum(abs(coverage[_norm(e)] - target) for e in edges)
                print(f"STUCK: no augmenting chain found after {augment_round} chains, "
                      f"remaining imbalance={imbalance}")
            return None
        _apply_chain(chain, trees, tree_edge_sets, coverage)

        # occasionally let single-hop passes mop up anything newly easy
        if augment_round % 20 == 0:
            _single_hop_pass(edges, trees, tree_edge_sets, coverage, target)

    if verbose:
        print(f"did not converge within {max_augment_rounds} augmenting rounds")
    return None


def verify_packing(G: nx.Graph, trees: list[nx.Graph], target: int) -> bool:
    n = G.number_of_nodes()
    coverage: Counter = Counter()
    for Tg in trees:
        assert Tg.number_of_edges() == n - 1
        assert nx.is_connected(Tg)
        for u, v in Tg.edges():
            assert G.has_edge(u, v)
            coverage[_norm((u, v))] += 1
    return all(coverage[_norm(e)] == target for e in G.edges())


if __name__ == "__main__":
    for n in [40, 50, 75, 100]:
        Kn = nx.complete_graph(n)
        m = Kn.number_of_edges()
        target = n - 1
        print(f"--- K{n} (m={m}) ---")
        t0 = time.perf_counter()
        result = build_tree_packing(Kn, m=m, target=target, seed=1, max_passes=5000, verbose=True)
        elapsed = time.perf_counter() - t0
        if result is None:
            print(f"  FAILED, {elapsed:.2f}s")
        else:
            ok = verify_packing(Kn, result, target)
            distinct = len({frozenset(_norm(e) for e in T.edges()) for T in result})
            print(f"  converged, {elapsed:.2f}s, verified={ok}, distinct trees={distinct}/{len(result)}")
