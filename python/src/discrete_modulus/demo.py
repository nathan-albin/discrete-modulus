"""
Small graphs and brute-force helpers for demonstrations.

These are meant for small pedagogical examples (as in the companion book),
not for production use — see `spanning_trees` in particular.
"""

from collections.abc import Iterator
from itertools import combinations
from typing import Any

import networkx as nx
import numpy as np

PosDict = dict[int, tuple[float, float]]
Edge = tuple[Any, Any]


def house_graph() -> tuple[nx.Graph, PosDict]:
    """
    Generates the house graph.

    Returns
    -------
    G : networkx graph
        The house graph.

    pos : dict
        Position dictionary for drawing the graph.
    """

    G = nx.cycle_graph(5)
    G.add_edge(0, 2)
    pos = {0: (0, 1), 1: (0.5, 1.87), 2: (1, 1), 3: (1, 0), 4: (0, 0)}

    return G, pos


def slashed_house_graph() -> tuple[nx.Graph, PosDict]:
    """
    Generates a house graph with a diagonal slash through it.

    Returns
    -------
    G : networkx graph
        The house graph.

    pos : dict
        Position dictionary for drawing the graph.
    """

    G, pos = house_graph()
    G.add_edge(0, 3)

    return G, pos


def nested_graph(n: int = 10) -> tuple[nx.Graph, PosDict]:
    """
    Generates a graph with three concentric "layers": a complete graph on
    `n` nodes, surrounded by two rings of `n` nodes each, with radial
    connections between consecutive layers.

    Parameters
    ----------
    n : int
        The number of nodes in each layer (`3*n` nodes total).

    Returns
    -------
    G : networkx graph
        The nested graph.

    pos : dict
        Position dictionary for drawing the graph, placing the three
        layers on concentric circles.
    """

    G: nx.Graph = nx.Graph()

    # complete graph on the innermost layer
    for i in range(n):
        for j in range(i + 1, n):
            G.add_edge(i, j)

    # connect each innermost node to three consecutive nodes in the
    # middle layer, and form a cycle within the middle layer
    for i in range(n):
        for b in (-1, 0, 1):
            j = (i + b) % n + n
            G.add_edge(i, j)
        j = (i + 1) % n + n
        G.add_edge(i + n, j)

    # radial connections to the outer layer, and a cycle within it
    for i in range(n):
        G.add_edge(i + n, i + 2 * n)
        j = (i + 1) % n + 2 * n
        G.add_edge(i + 2 * n, j)

    # position the nodes in concentric circles
    th = np.linspace(0, 2 * np.pi, n, endpoint=False)
    pos: PosDict = {i: (float(np.cos(th[i])), float(np.sin(th[i]))) for i in range(n)}
    pos.update({n + i: (2 * float(np.cos(th[i])), 2 * float(np.sin(th[i]))) for i in range(n)})
    pos.update({2 * n + i: (3 * float(np.cos(th[i])), 3 * float(np.sin(th[i]))) for i in range(n)})

    return G, pos


def spanning_trees(G: nx.Graph) -> Iterator[tuple[Edge, ...]]:
    """
    Generates all spanning trees of a graph.

    Parameters
    ----------
    G : networkx graph

    Returns
    -------
    generator
        Each item returned is a list of edges for a spanning tree.
        The generator will produce every tree before terminating.

    Notes
    -----
    The algorithm looks at ALL combinations of |V|-1 edges in G and
    determines which are trees.  This will be very very slow on large
    graphs, so use with care.
    """

    n = len(G.nodes)
    for T in combinations(G.edges, n - 1):
        H: nx.Graph = nx.Graph(T)
        if nx.is_tree(H):
            yield T
