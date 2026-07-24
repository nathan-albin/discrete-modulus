"""
Variant of column_gen.py's Phase-1 LP, scaled by m so the RHS is
all-integer (target = theta*m per edge, total = m for the count
constraint) instead of theta/1 -- testing whether floating-point
simplex lands on a nicer basis when its targets are exactly
representable in binary floating point, vs 0.1 which isn't.

x_T here is a tree COUNT (not a probability); divide by m to recover
the pmf. See conversation for why this differs from just passing
Fraction(1,10) through the same float-based LP: float(Fraction(1,10))
is bit-identical to 1/10, so that alone changes nothing. This changes
what accumulates as *rounding error through the whole pivoting
process*, which can change which of many degenerate alternate optima
simplex converges to.
"""
import networkx as nx
import numpy as np
from scipy.optimize import linprog


def column_generate_pmf_scaled(G, target, total, max_iters=300, verbose=True):
    edges = list(G.edges())
    m = len(edges)
    edge_idx = {frozenset(e): i for i, e in enumerate(edges)}

    working_trees = []

    def tree_indicator(tree_edges):
        vec = np.zeros(m)
        for e in tree_edges:
            vec[edge_idx[frozenset(e)]] = 1.0
        return vec

    T0 = list(nx.minimum_spanning_tree(G).edges())
    working_trees.append(tuple(T0))

    for it in range(max_iters):
        k = len(working_trees)
        A = np.zeros((m, k))
        for j, t in enumerate(working_trees):
            A[:, j] = tree_indicator(t)

        num_art = m + 1
        num_vars = k + num_art
        c = np.concatenate([np.zeros(k), np.ones(num_art)])

        A_eq = np.zeros((m + 1, num_vars))
        A_eq[:m, :k] = A
        A_eq[:m, k:k + m] = np.eye(m)
        A_eq[m, :k] = 1.0
        A_eq[m, k + m] = 1.0
        b_eq = np.concatenate([np.full(m, float(target)), [float(total)]])

        res = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * num_vars, method='highs')
        assert res.success, "restricted LP failed unexpectedly"
        phase1_obj = res.fun
        y = res.eqlin.marginals

        if verbose:
            print(f"iter {it}: working set size={k}, phase1 obj={phase1_obj:.6g}")

        if phase1_obj < 1e-6:
            lam = res.x[:k]
            support = [(working_trees[j], lam[j]) for j in range(k) if lam[j] > 1e-9]
            return support, it

        y_edge = y[:m]
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        for i, e in enumerate(edges):
            H.add_edge(*e, weight=y_edge[i])
        new_tree = list(nx.maximum_spanning_tree(H, weight='weight').edges())
        new_tree_key = tuple(new_tree)

        reduced_cost = 0 - (sum(y_edge[edge_idx[frozenset(e)]] for e in new_tree) + y[m])
        if reduced_cost > -1e-9 or new_tree_key in working_trees:
            if new_tree_key not in working_trees:
                working_trees.append(new_tree_key)
                continue
            return None, it

        working_trees.append(new_tree_key)

    return None, max_iters
