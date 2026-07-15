"""
Exact-rational (fractions.Fraction) version of wolfe_min_norm.py.

Motivation: we know a priori that eta* = theta * 1_C has denominator dividing
|C| (theta = (|V~|-1)/|C|), so the whole computation should be exactly
rational -- no floating-point tolerance checks (`> tol`, `>= tol - eps`)
should be needed at all, just exact `>` and `>=`.

Unlike the cdd.gmp column-generation attempt (column_gen_exact.py), which was
too slow to use as an inner-loop solver, Wolfe's minor cycle only ever solves
a SMALL (r+1)x(r+1) linear system, r = current active-set size (bounded by
Caratheodory, but empirically much smaller -- 3 on house). That's a much
cheaper operation than resolving a growing general-purpose LP (with O(m)
artificial variables) from scratch every iteration, which is what made
cdd.gmp impractical. This file checks whether that expectation holds up.
"""
import networkx as nx
from fractions import Fraction as F


def solve_exact(A, b):
    """Exact Gaussian elimination with partial pivoting. A: list of list of
    Fraction (n x n), b: list of Fraction (n). Returns list of Fraction."""
    n = len(A)
    M = [row[:] + [b[i]] for i, row in enumerate(A)]
    for col in range(n):
        pivot = next(r for r in range(col, n) if M[r][col] != 0)
        M[col], M[pivot] = M[pivot], M[col]
        pv = M[col][col]
        M[col] = [x / pv for x in M[col]]
        for r in range(n):
            if r != col and M[r][col] != 0:
                factor = M[r][col]
                M[r] = [M[r][k] - factor * M[col][k] for k in range(n + 1)]
    return [M[r][n] for r in range(n)]


def wolfe_min_norm_pmf_exact(G, max_major=200, max_minor=200, verbose=True, init_tree=None):
    edges = list(G.edges())
    m = len(edges)
    edge_idx = {frozenset(e): i for i, e in enumerate(edges)}

    def tree_vec(tree_edges):
        v = [F(0)] * m
        for e in tree_edges:
            v[edge_idx[frozenset(e)]] = F(1)
        return v

    def dot(a, b):
        return sum(x * y for x, y in zip(a, b))

    def mst_vec(weights):
        H = nx.Graph()
        H.add_nodes_from(G.nodes())
        for i, e in enumerate(edges):
            H.add_edge(*e, weight=weights[i])
        T = tuple(nx.minimum_spanning_tree(H, weight='weight').edges())
        return tree_vec(T), T

    if init_tree is not None:
        key0, v0 = init_tree, tree_vec(init_tree)
    else:
        v0, key0 = mst_vec([F(0)] * m)
    S = [key0]
    V = [v0]
    lam = [F(1)]
    x = v0[:]

    major_iters = 0
    total_minor = 0
    evictions = 0
    eviction_log = []

    for _ in range(max_major):
        major_iters += 1
        v_star, key_star = mst_vec(x)

        if dot(x, v_star) >= dot(x, x):
            if verbose:
                print(f"optimal after {major_iters} major, {total_minor} minor iterations, "
                      f"{evictions} evictions (exact)")
            return x, list(zip(S, lam)), major_iters, total_minor, eviction_log

        if key_star not in S:
            S.append(key_star)
            V.append(v_star)
            lam.append(F(0))

        while True:
            total_minor += 1
            r = len(V)
            Gram = [[dot(V[i], V[j]) for j in range(r)] for i in range(r)]
            A = [[Gram[i][j] for j in range(r)] + [F(1)] for i in range(r)]
            A.append([F(1)] * r + [F(0)])
            b = [F(0)] * r + [F(1)]
            mu = solve_exact(A, b)[:r]

            if all(v > 0 for v in mu):
                lam = mu
                x = [sum(lam[i] * V[i][e] for i in range(r)) for e in range(m)]
                break

            theta = F(1)
            for i in range(r):
                if mu[i] < lam[i]:
                    theta = min(theta, lam[i] / (lam[i] - mu[i]))
            lam = [lam[i] + theta * (mu[i] - lam[i]) for i in range(r)]
            x = [sum(lam[i] * V[i][e] for i in range(r)) for e in range(m)]
            keep = [i for i in range(r) if lam[i] > 0]
            evicted = [S[i] for i in range(r) if i not in keep]
            for et in evicted:
                eviction_log.append(et)
                if verbose:
                    print(f"  evicted: {et}")
            evictions += len(evicted)
            S = [S[i] for i in keep]
            V = [V[i] for i in keep]
            lam = [lam[i] for i in keep]

    if verbose:
        print("did not converge within max_major")
    return x, list(zip(S, lam)), major_iters, total_minor, eviction_log


if __name__ == "__main__":
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 4)]
    G = nx.Graph()
    G.add_nodes_from(range(5))
    G.add_edges_from(edges)

    print("=== cold start (exact) ===")
    x, support, major, minor, evicted = wolfe_min_norm_pmf_exact(G)
    print(f"x (should be uniform 2/3, exactly): {x}")
    for t, w in support:
        print(f"  {t}: weight={w}")
    print(f"sum of weights = {sum(w for _, w in support)}")

    print("\n=== forced start from a known-forbidden tree (exact) ===")
    forbidden_tree = ((0, 1), (1, 2), (2, 3), (3, 4))
    x2, support2, major2, minor2, evicted2 = wolfe_min_norm_pmf_exact(G, init_tree=forbidden_tree)
    print(f"x: {x2}")
    was_forbidden_evicted = any(frozenset(t) == frozenset(forbidden_tree) for t in evicted2)
    print(f"forced-in forbidden tree was evicted? {was_forbidden_evicted}")
    for t, w in support2:
        print(f"  {t}: weight={w}")
