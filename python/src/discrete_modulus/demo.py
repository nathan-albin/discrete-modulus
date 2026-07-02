"""
Small graphs and brute-force helpers for demonstrations.

These are meant for small pedagogical examples (as in the companion book),
not for production use — see `spanning_trees` in particular.
"""

from collections.abc import Iterator
from itertools import combinations
from typing import Any

import networkx as nx

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
