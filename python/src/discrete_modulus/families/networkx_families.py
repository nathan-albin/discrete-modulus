"""
Functor classes for various families of objects implemented
in NetworkX.
"""

from collections.abc import Iterable

import networkx as nx
import numpy as np

from ..protocols import ExactArray, FloatArray, ShortestResult


class ShortestConnectingPath:
    """
    Functor class for finding the shortest rho-length path between two sets of nodes.

    Implements `ShortestObjectFinder` for the family of paths connecting
    any node in `S` to any node in `T`.
    """

    # the dummy source and target node names
    src = "__source__"
    tgt = "__target__"

    def __init__(self, G: nx.Graph, S: Iterable, T: Iterable) -> None:
        """
        Parameters
        ----------
        G : networkx graph
            The graph the family of paths lives in.

        S : iterable of nodes
            The set of allowed path start nodes.

        T : iterable of nodes
            The set of allowed path end nodes.

        Notes
        -----
        This mutates `G` by adding an `'enum'` edge attribute (an index
        into `rho`/the usage matrix). A copy of `G`, with dummy source
        and target nodes attached, is kept internally for the
        shortest-path search; `G` itself is otherwise left untouched.
        """

        # remember the graph, source and target sets
        self.G = G
        self.S = S
        self.T = T

        # enumerate the edges so we can keep track of them
        # when processing a path
        for i, (u, v) in enumerate(G.edges()):
            G[u][v]["enum"] = i

        # make a copy of G to work on
        self.H = G.copy()

        # add dummy source and target nodes
        self.H.add_node(self.src)
        self.H.add_node(self.tgt)

        # link the dummy nodes
        for v in S:
            self.H.add_edge(self.src, v, rho=0)
        for v in T:
            self.H.add_edge(v, self.tgt, rho=0)

    def __call__(self, rho: FloatArray | ExactArray, tol: float) -> ShortestResult:
        """
        Finds the shortest rho-length path from `S` to `T`.

        Parameters
        ----------
        rho : numpy array
            The current density, one entry per edge of `G` (in the order
            `G.edges()` iterates). May be an `ExactArray` for an exact
            result (see `ExactArray`).

        tol : float
            Unused; accepted to satisfy the `ShortestObjectFinder`
            interface.

        Returns
        -------
        ShortestResult
            `cons` is the path found, as a list of nodes from `S` to `T`
            (the dummy source/target nodes are already trimmed off).
            `n` is its usage vector, with the same dtype as `rho`.
        """

        # assign rho to the graph edges
        for i, (u, v) in enumerate(self.G.edges()):
            self.H[u][v]["rho"] = rho[i]

        # find the shortest path
        p = nx.shortest_path(self.H, self.src, self.tgt, weight="rho")

        # the actual path omits the source and target dummy nodes
        p = p[1:-1]

        # form the row vector. mypy can't infer, from a union-typed rho,
        # that dtype=rho.dtype produces a same-union-member array.
        n: FloatArray | ExactArray = np.zeros(rho.shape, dtype=rho.dtype)  # type: ignore[assignment]
        for i in range(len(p) - 1):
            n[self.G[p[i]][p[i + 1]]["enum"]] = 1

        return ShortestResult(p, n)


class MinimumSpanningTree:
    """
    Functor class for finding the minimum rho-length spanning tree.

    Implements `ShortestObjectFinder` for the family of spanning trees
    of `G`. `G` may be a `nx.Graph` or a `nx.MultiGraph` -- a shrunk
    multigraph produced by repeatedly contracting a graph's vertices
    (as the C++ solver's rounds do, and as `core_deflation` does when
    contracting a core to a point) generally has parallel edges, so both
    are supported: with a `MultiGraph`, `cons` disambiguates parallel
    edges as `(u, v, key)` triples instead of plain `(u, v)` pairs.
    """

    def __init__(self, G: nx.Graph) -> None:
        """
        Parameters
        ----------
        G : networkx graph or multigraph
            The graph whose spanning trees make up the family.

        Notes
        -----
        This mutates `G` by adding an `'enum'` edge attribute (an index
        into `rho`/the usage matrix), and, on each call, a `'rho'` edge
        attribute holding the most recently assigned density. Iterating
        with `data=True` and mutating the yielded attribute dict
        in place (rather than indexing `G[u][v]`, which for a
        `MultiGraph` is a dict-of-parallel-edges, not a single edge's
        attributes) keeps this correct for both graph types.
        """

        # remember the graph
        self.G = G
        self.is_multigraph = G.is_multigraph()

        # enumerate the edges so we can keep track of them when
        # processing a spanning tree
        for i, (_u, _v, data) in enumerate(G.edges(data=True)):
            data["enum"] = i

    def __call__(self, rho: FloatArray | ExactArray, tol: float) -> ShortestResult:
        """
        Finds a minimum rho-length spanning tree of `G`.

        Parameters
        ----------
        rho : numpy array
            The current density, one entry per edge of `G` (in the order
            `G.edges()` iterates). May be an `ExactArray` for an exact
            result (see `ExactArray`).

        tol : float
            Unused; accepted to satisfy the `ShortestObjectFinder`
            interface.

        Returns
        -------
        ShortestResult
            `cons` is the list of edges in the minimum spanning tree --
            `(u, v)` pairs for a plain `Graph`, `(u, v, key)` triples for
            a `MultiGraph`. `n` is its usage vector, with the same dtype
            as `rho`.
        """

        # assign rho to the graph edges
        for i, (_u, _v, data) in enumerate(self.G.edges(data=True)):
            data["rho"] = rho[i]

        # form the row vector. mypy can't infer, from a union-typed rho,
        # that dtype=rho.dtype produces a same-union-member array.
        n: FloatArray | ExactArray = np.zeros(rho.shape, dtype=rho.dtype)  # type: ignore[assignment]

        if self.is_multigraph:
            # keys=True disambiguates which parallel edge the MST used
            # -- needed both to look up its 'enum' index below and so
            # `cons` identifies a genuine spanning tree, not just a
            # multiset of vertex pairs.
            T = list(nx.minimum_spanning_edges(self.G, weight="rho", keys=True, data=False))
            for u, v, k in T:
                n[self.G[u][v][k]["enum"]] = 1
        else:
            T = list(nx.minimum_spanning_edges(self.G, weight="rho", data=False))
            for u, v in T:
                n[self.G[u][v]["enum"]] = 1

        return ShortestResult(T, n)
