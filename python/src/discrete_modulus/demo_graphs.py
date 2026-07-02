"""
Small graphs for various demonstrations.
"""

import networkx as nx

PosDict = dict[int, tuple[float, float]]


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
