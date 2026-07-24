"""
Exact-rational variant of column_gen.py's Phase-1 column generation, using
cdd.gmp (pycddlib's GMP-backed exact-arithmetic LP solver) instead of scipy's
floating-point linprog. Answers: "would pycddlib help here?" -- via its
cdd.gmp submodule (not the default cdd module, which is float-only despite
accepting Fraction inputs, silently converted to float with no error).

Scaling verdict: NOT recommended as the inner-loop solver for column
generation, despite doing better than scipy on the tiny house-graph case
below (2 iterations vs. 5, exact throughout, no separate verification pass
needed). Stress-tested the same way as column_gen.py (complete graphs K_n):
K_10 (m=45 -- the *smallest* case tested, which scipy/HiGHS solves in 0.15s)
still hadn't converged after 6.5 minutes of CPU time and had to be killed.
cdd's LP solver is a much simpler implementation than HiGHS (its primary use
in this codebase is polyhedron vertex/facet enumeration, not competitively
tuned simplex), and every arithmetic op costs far more under GMP rationals
than hardware floats -- both costs stack on top of this prototype's
from-scratch-every-iteration inefficiency (shared with column_gen.py).

Recommended use instead (see Certification_Plan.md Sec.5.1's exactness note):
run column_gen.py (float, fast) to discover which small set of trees form the
support, then use cdd.gmp -- or plain Fraction-based Gaussian elimination --
only for the small *final* linear system over that fixed support. That final
solve is cheap regardless of solver; it's the repeated-from-scratch inner
loop that doesn't scale here.
"""
import networkx as nx
import cdd.gmp as gmp
from fractions import Fraction as F


def column_generate_pmf_exact(G, theta, max_iters=200, verbose=True):
    edges = list(G.edges())
    m = len(edges)
    edge_idx = {frozenset(e): i for i, e in enumerate(edges)}
    theta = F(theta)

    working_trees = [tuple(nx.minimum_spanning_tree(G).edges())]

    for it in range(max_iters):
        k = len(working_trees)
        num_vars = k + m + 1  # lambda_1..k, artificial_1..m, artificial_0 (normalization)

        rows = []
        lin_set = set()

        # equality rows: marginal constraints (m of them)
        for e_i in range(m):
            row = [F(-theta)] + [F(0)] * num_vars
            target_edge = frozenset(edges[e_i])
            for j, t in enumerate(working_trees):
                if any(frozenset(e) == target_edge for e in t):
                    row[1 + j] = F(1)
            row[1 + k + e_i] = F(1)  # artificial for this row
            rows.append(row)
            lin_set.add(len(rows) - 1)

        # equality row: normalization
        row = [F(-1)] + [F(1)] * k + [F(0)] * m + [F(1)]
        rows.append(row)
        lin_set.add(len(rows) - 1)

        # nonnegativity rows for all variables
        for j in range(num_vars):
            row = [F(0)] * (num_vars + 1)
            row[1 + j] = F(1)
            rows.append(row)

        obj_func = [F(0)] + [F(0)] * k + [F(1)] * (m + 1)

        mat = gmp.matrix_from_array(rows, lin_set=lin_set, rep_type=gmp.RepType.INEQUALITY,
                                     obj_type=gmp.LPObjType.MIN, obj_func=obj_func)
        lp = gmp.linprog_from_matrix(mat)
        gmp.linprog_solve(lp, gmp.LPSolverType.DUAL_SIMPLEX)
        assert lp.status == gmp.LPStatusType.OPTIMAL, f"LP not optimal: {lp.status}"

        phase1_obj = lp.obj_value
        if verbose:
            print(f"iter {it}: working set size={k}, phase1 obj={phase1_obj}")

        if phase1_obj == 0:
            lam = lp.primal_solution[:k]
            support = [(working_trees[j], lam[j]) for j in range(k) if lam[j] > 0]
            return support, it

        # dual values: index-value pairs over cdd's internal array, which is
        # laid out as [original rows as given to matrix_from_array]
        # + [negated copies of just the lin_set (equality) rows, in the same
        # relative order] + [the objective row]. NOT interleaved pairs -- the
        # negated copies are all appended together after every original row.
        y = [F(0)] * len(lp.array)
        for idx, val in lp.dual_solution:
            y[idx] = val
        num_orig_rows = m + 1 + num_vars  # m marginal + 1 normalization + nonneg rows
        neg_offset = num_orig_rows  # where negated equality rows start
        # negated relative to scipy's convention: cdd frames constraints as
        # 0 <= b+Ax (vs. the standard Ax=b), which flips the dual's sign.
        y_edge = [y[neg_offset + e_i] - y[e_i] for e_i in range(m)]
        y0 = y[neg_offset + m] - y[m]

        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        for i, e in enumerate(edges):
            H.add_edge(*e, weight=y_edge[i])
        new_tree = list(nx.maximum_spanning_tree(H, weight='weight').edges())
        new_tree_key = tuple(new_tree)

        reduced_cost = F(0) - (sum(y_edge[edge_idx[frozenset(e)]] for e in new_tree) + y0)
        if verbose:
            print(f"   priced tree {new_tree}, reduced cost={reduced_cost}")
        if new_tree_key in working_trees:
            return None, it  # stalled
        working_trees.append(new_tree_key)

    return None, max_iters


if __name__ == "__main__":
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 4)]
    G = nx.Graph()
    G.add_nodes_from(range(5))
    G.add_edges_from(edges)
    theta = F(2, 3)

    support, iters = column_generate_pmf_exact(G, theta)
    print(f"\nConverged in {iters} iterations")
    total = F(0)
    for t, w in support:
        print(f"  {t}: weight={w}")
        total += w
    print(f"sum of weights = {total}")

    # independent exact check of marginals
    usage = {frozenset(e): F(0) for e in edges}
    for t, w in support:
        for e in t:
            usage[frozenset(e)] += w
    print("marginals:", usage, "all == theta?", all(v == theta for v in usage.values()))
