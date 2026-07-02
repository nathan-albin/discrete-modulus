"""
Functor classes for various families of objects implemented
in NetworkX.
"""

from collections.abc import Iterable

import networkx as nx
import numpy as np

from ..protocols import FloatArray, ShortestResult


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

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult:
        """
        Finds the shortest rho-length path from `S` to `T`.

        Parameters
        ----------
        rho : numpy array
            The current density, one entry per edge of `G` (in the order
            `G.edges()` iterates).

        tol : float
            Unused; accepted to satisfy the `ShortestObjectFinder`
            interface.

        Returns
        -------
        ShortestResult
            `cons` is the path found, as a list of nodes from `S` to `T`
            (the dummy source/target nodes are already trimmed off).
            `n` is its usage vector.
        """

        # assign rho to the graph edges
        for i, (u, v) in enumerate(self.G.edges()):
            self.H[u][v]["rho"] = rho[i]

        # find the shortest path
        p = nx.shortest_path(self.H, self.src, self.tgt, weight="rho")

        # the actual path omits the source and target dummy nodes
        p = p[1:-1]

        # form the row vector
        n = np.zeros(rho.shape)
        for i in range(len(p) - 1):
            n[self.G[p[i]][p[i + 1]]["enum"]] = 1

        return ShortestResult(p, n)


class MinimumSpanningTree:
    """
    Functor class for finding the minimum rho-length spanning tree.

    Implements `ShortestObjectFinder` for the family of spanning trees
    of `G`.
    """

    def __init__(self, G: nx.Graph) -> None:
        """
        Parameters
        ----------
        G : networkx graph
            The graph whose spanning trees make up the family.

        Notes
        -----
        This mutates `G` by adding an `'enum'` edge attribute (an index
        into `rho`/the usage matrix), and, on each call, a `'rho'` edge
        attribute holding the most recently assigned density.
        """

        # remember the graph
        self.G = G

        # enumerate the edges so we can keep track of them when
        # processing a spanning tree
        for i, (u, v) in enumerate(G.edges()):
            G[u][v]["enum"] = i

    def __call__(self, rho: FloatArray, tol: float) -> ShortestResult:
        """
        Finds a minimum rho-length spanning tree of `G`.

        Parameters
        ----------
        rho : numpy array
            The current density, one entry per edge of `G` (in the order
            `G.edges()` iterates).

        tol : float
            Unused; accepted to satisfy the `ShortestObjectFinder`
            interface.

        Returns
        -------
        ShortestResult
            `cons` is the list of edges in the minimum spanning tree.
            `n` is its usage vector.
        """

        # assign rho to the graph edges
        for i, (u, v) in enumerate(self.G.edges()):
            self.G[u][v]["rho"] = rho[i]

        # find a minimum spanning tree
        T = list(nx.minimum_spanning_edges(self.G, weight="rho", data=False))

        # form the row vector
        n = np.zeros(rho.shape)
        for u, v in T:
            n[self.G[u][v]["enum"]] = 1

        return ShortestResult(T, n)
