"""
Shared, plain (non-fixture) utilities for discrete_modulus tests.
"""

from __future__ import annotations

import networkx as nx
import numpy as np

from discrete_modulus.protocols import FloatArray


def edge_index(G: nx.Graph) -> dict[frozenset, int]:
    """
    Maps each edge of G to a column index, in the same order the
    package's own functors assign via their internal edge 'enum'
    bookkeeping (i.e. the order `G.edges()` iterates).
    """
    return {frozenset(e): i for i, e in enumerate(G.edges())}


def path_edges(path: list) -> list[tuple]:
    """Converts a node path (as returned by e.g. `nx.all_simple_paths`) into
    a list of edges."""
    return list(zip(path, path[1:], strict=False))


def full_usage_matrix(
    objects: list[list[tuple]], index: dict[frozenset, int], m: int
) -> FloatArray:
    """
    Builds a dense usage matrix (one row per object) for a family given
    explicitly as a list of edge lists, e.g. spanning trees (from
    `demo.spanning_trees`) or paths (via `path_edges`).
    """
    N = np.zeros((len(objects), m))
    for i, obj in enumerate(objects):
        for e in obj:
            N[i, index[frozenset(e)]] = 1
    return N
