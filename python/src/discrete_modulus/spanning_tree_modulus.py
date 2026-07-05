"""
Exact spanning tree modulus via Cunningham's algorithm.

This implements the algorithm of Albin, Kottegoda, and Poggi-Corradini,
"An Exact-Arithmetic Algorithm for Spanning Tree Modulus," Networks 85(4),
412-424, which builds on Cunningham's matroid-greedy algorithm for
polymatroid bases.

Consider an undirected graph G=(V,E). The rank function `rank(G, J)` gives
the rank of an edge set J, and the polymatroid P(f) is the set of
non-negative edge functions x with x(J) <= f(J) for every J subseteq E. A
P(f)-basis of a non-negative edge function y is a maximal x in P(f) with
x <= y elementwise. Cunningham's greedy algorithm (`cunningham_min`) finds
such a basis by increasing x on each edge in turn, using max flow
(`_solve_subproblem`) to detect when a further increase would leave P(f).

To keep everything in exact integer arithmetic, a P(f)-basis of the
constant rational function y = p/q is found instead as a P(qf)-basis of
the constant integer function q. `graph_vulnerability` uses this to
locate, by binary search, the vulnerability theta(G) -- the smallest p/q
for which a P(qf)-basis of q has weight >= q*(|V|-1) -- along with a tight
edge set. `spanning_tree_modulus` repeatedly extracts theta(G) on
remaining components to build up eta*, the exact spanning tree modulus:
the edge weighting whose blocking dual is Chopra's family of feasible
partitions (see the companion book).
"""

from __future__ import annotations

from collections import UserDict
from collections.abc import Iterable
from fractions import Fraction
from typing import Any
from warnings import warn

import networkx as nx

Edge = tuple[Any, Any]
EdgeValue = int | Fraction

_SOURCE = "__source"
_TARGET = "__target"


def rank(G: nx.Graph, J: Iterable[Edge]) -> int:
    """
    Computes the rank of the edge set `J` in `G`.

    Parameters
    ----------
    G : networkx graph

    J : iterable of edges
        A subset of `G`'s edges.

    Returns
    -------
    int
        `|V| - Q(G_J)`, where `G_J` is the subgraph of `G` on the same
        vertex set keeping only the edges in `J`, and `Q` counts
        connected components (including isolated vertices).

    Notes
    -----
    Not used internally by `spanning_tree_modulus`; included for building
    intuition (see the companion book).
    """

    H: nx.Graph = nx.Graph()
    H.add_nodes_from(G.nodes)
    H.add_edges_from(J)

    return len(G.nodes) - nx.number_connected_components(H)


class EdgeFunction(UserDict[frozenset[Any], EdgeValue]):
    """
    An edge function on a graph, with the symmetry `x(u,v) == x(v,u)`
    built in by storing each edge as a `frozenset`.

    Notes
    -----
    Keys are converted to `frozenset` on every access, so any 2-element
    iterable naming an edge's endpoints is accepted; there is no check
    that the edge actually belongs to the graph the function was created
    for.
    """

    def __init__(self, G: nx.Graph) -> None:
        """
        Initializes the EdgeFunction as the zero function on the edges
        of `G`.
        """

        super().__init__()
        self.update({frozenset(e): 0 for e in G.edges})

    def __getitem__(self, e: Edge) -> EdgeValue:  # type: ignore[override]
        return super().__getitem__(frozenset(e))

    def __setitem__(self, e: Edge, v: EdgeValue) -> None:  # type: ignore[override]
        super().__setitem__(frozenset(e), v)

    def __str__(self) -> str:
        items = ["({},{}): {}".format(*sorted(e), v) for e, v in self.data.items()]
        return ", ".join(items)


def create_flow_graph(G: nx.Graph) -> nx.Graph:
    """
    Builds the auxiliary flow graph used by `cunningham_min`.

    Parameters
    ----------
    G : networkx graph

    Returns
    -------
    networkx graph
        A copy of `G` with `"__source"` and `"__target"` nodes added,
        each connected to every node of `G`. Edge capacities are not set
        here; `cunningham_min` (via `_solve_subproblem`) fills them in on
        every call, since they depend on the current edge function `x`.
    """

    F: nx.Graph = nx.Graph(G)
    F.add_node(_SOURCE)
    F.add_node(_TARGET)
    F.add_edges_from([(_SOURCE, v) for v in G.nodes])
    F.add_edges_from([(_TARGET, v) for v in G.nodes])

    return F


def _solve_subproblem(
    G: nx.Graph, F: nx.Graph, x: EdgeFunction, e: Edge, q: int
) -> tuple[int, set[Edge]]:
    """
    One max-flow step of Cunningham's algorithm: finds how far `x` can be
    increased on edge `e` without leaving the polymatroid `P(qf)`.

    Parameters
    ----------
    G : networkx graph

    F : networkx graph
        The flow graph for `G`, from `create_flow_graph`.

    x : EdgeFunction
        The current point in `P(qf)`.

    e : edge
        The edge being incremented.

    q : int

    Returns
    -------
    eps : int
        The maximum amount `x(e)` can be increased.

    crit_edges : set of edges
        The critical (tight) edge set found by the min cut.
    """

    n = G.number_of_nodes()

    # capacities between "regular" nodes
    for u, v in G.edges:
        F[u][v]["capacity"] = x[(u, v)]

    # fixed capacities to the target
    for v in G.nodes:
        F[v][_TARGET]["capacity"] = 2 * q

    # capacities from the source. Edges to the endpoints of e are given
    # an "unlimited" capacity so the min cut never has to pass through
    # them; the total capacity into the target is 2*q*n, so anything
    # larger than that can never be the bottleneck. Using a finite bound
    # (rather than float('inf')) keeps the whole computation in exact
    # integer arithmetic.
    unlimited = 2 * q * n + 1
    for v in G.nodes:
        if v in e:
            F[_SOURCE][v]["capacity"] = unlimited
        else:
            F[_SOURCE][v]["capacity"] = sum(x[(u, v)] for u in G[v])

    # perform the minimum cut
    cut_value, partition = nx.minimum_cut(F, _SOURCE, _TARGET)

    # find epsilon from the cut value
    eps = cut_value // 2 - q - sum(x[edge] for edge in G.edges)

    # the critical set is the partition containing the source
    crit_set = partition[0] if _SOURCE in partition[0] else partition[1]
    crit_set = crit_set - {_SOURCE}

    # edges contained in the critical set
    crit_edges = {(u, v) for u, v in G.edges if u in crit_set and v in crit_set}

    return eps, crit_edges


def cunningham_min(G: nx.Graph, F: nx.Graph, p: int, q: int) -> tuple[EdgeFunction, set[Edge]]:
    """
    Finds a P(qf)-basis for the constant function p, along with a tight
    set, using Cunningham's greedy algorithm.

    Parameters
    ----------
    G : networkx graph

    F : networkx graph
        The flow graph for `G`, from `create_flow_graph`.

    p : int

    q : int
        Together, `p/q` is the rational constant whose P(f)-basis is
        being sought (see the module docstring for the integer-arithmetic
        reformulation this implements).

    Returns
    -------
    x : EdgeFunction
        The P(qf)-basis found.

    A : set of edges
        A tight set for `x` (i.e. `x(A) == q * f(A)`).
    """

    x = EdgeFunction(G)
    A: set[Edge] = set()

    for e in G.edges:
        if e in A:
            continue

        eps: EdgeValue
        eps, crit_edges = _solve_subproblem(G, F, x, e, q)

        if eps < p - x[e]:
            A |= crit_edges
        else:
            eps = p - x[e]
        x[e] += eps

    return x, A


def graph_vulnerability(G: nx.Graph, F: nx.Graph) -> tuple[Fraction, set[Edge]]:
    """
    Finds the vulnerability theta(G) of a graph by binary search, along
    with an optimal tight set.

    Parameters
    ----------
    G : networkx graph

    F : networkx graph
        The flow graph for `G`, from `create_flow_graph`.

    Returns
    -------
    theta : Fraction
        The vulnerability of `G`.

    J : set of edges
        A tight edge set achieving `theta`.
    """

    m, n = len(G.edges), len(G.nodes)

    Theta = sorted({Fraction(p, q) for q in range(1, m + 1) for p in range(1, min(n - 1, q) + 1)})

    crit_set: set[Edge] = set()
    lb, ub = 0, len(Theta)

    while lb < ub:
        mid = (ub + lb) // 2
        p, q = Theta[mid].numerator, Theta[mid].denominator

        x, J = cunningham_min(G, F, p, q)
        xE = sum(x.values())

        if xE >= q * (n - 1):
            ub = mid
            crit_set = J
        else:
            lb = mid + 1

    return Theta[lb], crit_set


def spanning_tree_modulus(G: nx.Graph, verbose: bool = False) -> EdgeFunction:
    """
    Computes the exact spanning tree modulus of `G` using Cunningham's
    algorithm.

    Parameters
    ----------
    G : networkx graph

    verbose : bool
        If True, prints a progress table to stdout as edges are assigned
        their eta* value.

    Returns
    -------
    EdgeFunction
        eta*: the exact spanning tree modulus edge weighting, whose
        blocking dual is Chopra's family of feasible partitions (see the
        companion book's chapter on families and blocking duality).

    Notes
    -----
    This is an *exact*, combinatorial alternative to the general,
    iterative/approximate solver in `discrete_modulus.algorithms.modulus`,
    specific to the spanning-tree/feasible-partition case. See the module
    docstring for the algorithm and its source.
    """

    eta_star = EdgeFunction(G)
    remain = len(G.edges)

    # (in case G is disconnected, process each connected component
    # separately)
    process = [G.subgraph(c).copy() for c in nx.connected_components(G)]

    if verbose:
        print(
            "| {:^12} | {:^12} | {:^12} | {:^12} |".format(
                "eta", "num edge", "edge_remain", "comp remain"
            )
        )
        print(("+" + "-" * 14) * 4 + "+")

    while process:
        H = process.pop()

        if len(H.edges) == 0:
            continue

        F = create_flow_graph(H)

        theta, J = graph_vulnerability(H, F)

        m = len(H.edges)
        p, q = theta.numerator, theta.denominator
        if len(J) == m:
            warn("Got entire edge set as tight. Rerunning.", stacklevel=2)
            pp = p * m**2 - q
            qq = q * m**2
            _, J = cunningham_min(H, F, pp, qq)

        # complement of the tight set: these edges get eta* = theta
        crit_set = [(u, v) for u, v in H.edges if (u, v) not in J and (v, u) not in J]

        for e in crit_set:
            eta_star[e] = theta

        # remove critical edges and split into connected components
        H.remove_edges_from(crit_set)
        comps = [H.subgraph(c).copy() for c in nx.connected_components(H)]
        assert theta == Fraction(len(comps) - 1, len(crit_set))
        process.extend(comps)

        remain -= len(crit_set)
        if verbose:
            print(f"| {str(theta):^12} | {len(crit_set):^12} | {remain:^12} | {len(process):^12} |")

    return eta_star
