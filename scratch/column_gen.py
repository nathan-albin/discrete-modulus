"""
Prototype: column generation for the "medium gap" pmf construction.

Given a shrunk graph G~ = (V~, C) where the uniform vector theta*1_C is known
to lie in the spanning-tree polytope, find a SPARSE pmf on spanning trees of
G~ realizing marginal usage theta on every edge, via Phase-1-simplex column
generation, with the pricing step realized as a max-weight spanning tree
computation (Kruskal/networkx), not full enumeration.

See Certification_Plan.md §5.1 for the writeup this validates: exactly 2 of
the house graph's 11 spanning trees can never appear in any feasible pmf's
support, and this algorithm converges to a 3-tree support that avoids both,
without ever enumerating all 11.
"""
import itertools
import networkx as nx
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction


def column_generate_pmf(G, theta, max_iters=200, verbose=True):
    edges = list(G.edges())
    m = len(edges)
    n = G.number_of_nodes()
    edge_idx = {frozenset(e): i for i, e in enumerate(edges)}

    working_trees = []  # list of frozenset-edge-index tuples

    def tree_indicator(tree_edges):
        vec = np.zeros(m)
        for e in tree_edges:
            vec[edge_idx[frozenset(e)]] = 1.0
        return vec

    # bootstrap with one arbitrary spanning tree (Kruskal, unit weights)
    T0 = list(nx.minimum_spanning_tree(G).edges())
    working_trees.append(tuple(T0))

    for it in range(max_iters):
        k = len(working_trees)
        A = np.zeros((m, k))
        for j, t in enumerate(working_trees):
            A[:, j] = tree_indicator(t)

        # Phase-1 LP: minimize sum of artificials
        # variables: lambda (k) >=0, artificial a_e (m) >=0 for marginal rows,
        # artificial a0 (1) >=0 for normalization row
        num_art = m + 1
        num_vars = k + num_art
        c = np.concatenate([np.zeros(k), np.ones(num_art)])

        A_eq = np.zeros((m + 1, num_vars))
        A_eq[:m, :k] = A
        A_eq[:m, k:k + m] = np.eye(m)
        A_eq[m, :k] = 1.0
        A_eq[m, k + m] = 1.0
        b_eq = np.concatenate([np.full(m, theta), [1.0]])

        res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * num_vars, method='highs')
        assert res.success, "restricted LP failed unexpectedly"
        phase1_obj = res.fun
        y = res.eqlin.marginals  # dual prices, length m+1

        if verbose:
            print(f"iter {it}: working set size={k}, phase1 obj={phase1_obj:.6g}")

        if phase1_obj < 1e-9:
            lam = res.x[:k]
            support = [(working_trees[j], lam[j]) for j in range(k) if lam[j] > 1e-9]
            return support, it

        # pricing: maximize sum_{e in T} y_e + y0 over spanning trees T
        # i.e. max-weight spanning tree w.r.t. weights y_e (plus constant y0*1, irrelevant to argmax)
        y_edge = y[:m]
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        for i, e in enumerate(edges):
            H.add_edge(*e, weight=y_edge[i])
        new_tree = list(nx.maximum_spanning_tree(H, weight='weight').edges())
        new_tree_key = tuple(new_tree)

        # reduced cost check (avoid re-adding same tree / infinite loop)
        reduced_cost = 0 - (sum(y_edge[edge_idx[frozenset(e)]] for e in new_tree) + y[m])
        if verbose:
            print(f"   priced tree {new_tree}, reduced cost={reduced_cost:.6g}")
        if reduced_cost > -1e-9 or new_tree_key in working_trees:
            # no improving column found (shouldn't happen until truly optimal/infeasible)
            if new_tree_key not in working_trees:
                working_trees.append(new_tree_key)
                continue
            return None, it  # stalled

        working_trees.append(new_tree_key)

    return None, max_iters


if __name__ == "__main__":
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 4)]
    G = nx.Graph()
    G.add_nodes_from(range(5))
    G.add_edges_from(edges)
    theta = 2 / 3

    support, iters = column_generate_pmf(G, theta)
    print(f"\nConverged in {iters} iterations")
    print("Support:")
    total = 0
    for t, w in support:
        print(f"  {t}: weight={w:.6f}")
        total += w
    print(f"sum of weights = {total:.6f}")
    forbidden = {frozenset([(0, 1), (1, 2), (2, 3), (3, 4)]), frozenset([(1, 2), (2, 3), (3, 4), (4, 0)])}
    used = {frozenset(t) for t, w in support}
    print(f"any forbidden tree in support? {any(f in used for f in forbidden)}")
