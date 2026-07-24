"""
Prototype: Wolfe's (1976) minimum-norm-point algorithm for the "medium gap"
pmf construction -- the established fix for the oscillation the user's
"Plus-1 algorithm" (vanilla Frank-Wolfe with a 1/(k+1) step size) exhibits.

Plus-1's update w_{k+1} = w_k + 1_{MST(w_k)} is exactly conditional-gradient
(Frank-Wolfe) descent on f(x) = ||x||^2 over conv(spanning trees), with a
fixed (not line-searched) step size -- a known-slow variant that famously
zig-zags when the minimizer lies on a low-dimensional face of the polytope
(which it does here: eta* is highly degenerate/sparse). Wolfe's algorithm
fixes exactly this via a "minor cycle" that projects onto the affine hull of
the current active set and, whenever that projection assigns a vertex a
negative coefficient, evicts it -- precisely "recognizing a bad tree and
backing off it". This is the same algorithm underlying Fujishige's
min-norm-point method for submodular function minimization (matroid rank
functions, e.g. the graphic matroid here, are submodular, so this problem is
a special case of that literature).
"""
import numpy as np
import networkx as nx
from fractions import Fraction as F


def wolfe_min_norm_pmf(G, max_major=200, max_minor=200, tol=1e-9, verbose=True, init_tree=None):
    """init_tree: optionally force the starting active set to a specific tree
    (a tuple of edges), to demonstrate/test the eviction mechanism directly
    (e.g. seeding with a known-forbidden tree -- see __main__ below)."""
    edges = list(G.edges())
    m = len(edges)
    edge_idx = {frozenset(e): i for i, e in enumerate(edges)}

    def tree_vec(tree_edges):
        v = np.zeros(m)
        for e in tree_edges:
            v[edge_idx[frozenset(e)]] = 1.0
        return v

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
        v0, key0 = mst_vec(np.zeros(m))
    S = [key0]
    V = [v0]
    lam = np.array([1.0])
    x = v0.copy()

    major_iters = 0
    total_minor = 0
    evictions = 0
    eviction_log = []
    for _ in range(max_major):
        major_iters += 1
        v_star, key_star = mst_vec(x)

        if np.dot(x, v_star) >= np.dot(x, x) - tol:
            if verbose:
                print(f"optimal after {major_iters} major, {total_minor} minor iterations, "
                      f"{evictions} evictions")
            return x, list(zip(S, lam)), major_iters, total_minor, eviction_log

        if key_star not in S:
            S.append(key_star)
            V.append(v_star)
            lam = np.append(lam, 0.0)

        while True:
            total_minor += 1
            Vm = np.array(V).T
            r = Vm.shape[1]
            Gram = Vm.T @ Vm
            A = np.zeros((r + 1, r + 1))
            A[:r, :r] = Gram
            A[:r, r] = 1
            A[r, :r] = 1
            b = np.zeros(r + 1)
            b[r] = 1
            mu = np.linalg.solve(A, b)[:r]

            if np.all(mu > tol):
                lam = mu
                x = Vm @ lam
                break

            theta = 1.0
            for i in range(r):
                if mu[i] < lam[i] - tol:
                    theta = min(theta, lam[i] / (lam[i] - mu[i]))
            lam = lam + theta * (mu - lam)
            x = Vm @ lam
            keep = [i for i in range(r) if lam[i] > tol]
            evicted = [S[i] for i in range(r) if i not in keep]
            for et in evicted:
                eviction_log.append(et)
                if verbose:
                    print(f"  evicted: {et}")
            evictions += len(evicted)
            S = [S[i] for i in keep]
            V = [V[i] for i in keep]
            lam = lam[keep]

    if verbose:
        print("did not converge within max_major")
    return x, list(zip(S, lam)), major_iters, total_minor, eviction_log


def _check_and_report(edges, support, theta=F(2, 3)):
    forbidden = {frozenset([(0, 1), (1, 2), (2, 3), (3, 4)]), frozenset([(1, 2), (2, 3), (3, 4), (4, 0)])}
    used = {frozenset(t) for t, w in support}
    print("support:")
    for t, w in support:
        print(f"  {t}: weight={w:.6f}")
    print(f"sum of weights = {sum(w for _, w in support):.6f}")
    print(f"any forbidden tree in support? {any(f in used for f in forbidden)}")

    usage = {frozenset(e): F(0) for e in edges}
    for t, w in support:
        wf = F(w).limit_denominator(10**6)
        for e in t:
            usage[frozenset(e)] += wf
    print("marginals (float weights, Fraction-summed):", usage)


if __name__ == "__main__":
    edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (1, 4)]
    G = nx.Graph()
    G.add_nodes_from(range(5))
    G.add_edges_from(edges)

    print("=== cold start ===")
    x, support, major, minor, evicted = wolfe_min_norm_pmf(G)
    print(f"x (should be uniform 2/3): {x}")
    _check_and_report(edges, support)

    print("\n=== forced start from a known-forbidden tree ===")
    forbidden_tree = ((0, 1), (1, 2), (2, 3), (3, 4))
    x2, support2, major2, minor2, evicted2 = wolfe_min_norm_pmf(G, init_tree=forbidden_tree)
    print(f"x (should still be uniform 2/3): {x2}")
    print(f"evicted trees: {evicted2}")
    was_forbidden_evicted = any(frozenset(t) == frozenset(forbidden_tree) for t in evicted2)
    print(f"forced-in forbidden tree was evicted? {was_forbidden_evicted}")
    _check_and_report(edges, support2)
