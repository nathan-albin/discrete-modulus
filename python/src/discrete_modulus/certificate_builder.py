"""
Builds a v4 certificate (`Certification_Plan.md` §6,
`scratch/certificate_schema.json`) from a C++ solver trace
(`solver_trace.hpp`) and the original input graph.

This is the "standalone tool" PR 2 of the certification plan calls for:
untrusted, "elaborate freely" code -- bugs here produce a certificate the
Lean verifier rejects, not a false "verified" result, so this module
favors clarity over defensiveness in most places, but still runs its own
cheap sanity checks (`validate_certificate`) before handing a certificate
off, since those catch builder bugs long before a Lean run would.

Pipeline, per round of the solver trace:

1. Recover the round's own working graph `h_k` exactly, as
   `g.subgraph(round.vertices)` -- valid because `spanning_tree_modulus`'s
   pieces only ever separate, never re-merge, and every `crit_set` edge
   provably connects two *different* subsequent pieces (a structural fact
   of Cunningham's tight-set construction, not an assumption): once an
   edge is dispatched, its two endpoints can never both reappear in a
   later round's vertex set, so no earlier round's dispatched edge can
   ever spuriously reappear when reconstructing a later `h_k` this way.
   (Confirmed computationally against a real multi-round trace before
   this module was written -- see `scratch/nested_trace_validation.py`.)
2. Shrink `h_k`'s pieces (its connected components after removing
   `crit_set`) to points, keeping `crit_set` as edges -- genuinely a
   `MultiGraph` in general (`scratch/nested_trace_validation.py` found
   multiplicity up to 3 on `examples/nested`), which is exactly what
   `pmf_construction.build_factored_pmf` already expects.
3. Run `build_factored_pmf` on the shrunk multigraph (deflation + Wolfe's
   algorithm per strictly-homogeneous piece, already implemented/tested).
4. Translate every piece's local edge indices into GLOBAL indices (into
   the certificate's own top-level `graph.edges` array), and append them,
   in order, to the certificate's flat `pieces` list.

Global edge indices are assigned round by round, in the order each
round's `crit_set` is recorded -- so the top-level `graph.edges` array is
built entirely from the trace itself, with no need to separately supply
or cross-check the original edge list's own ordering.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import networkx as nx

from .pmf_construction import build_factored_pmf


@dataclass(frozen=True)
class SolverTrace:
    """A parsed `solver_trace.hpp` trace: one `TraceRound` per round."""

    rounds: list[TraceRound]


@dataclass(frozen=True)
class TraceRound:
    vertices: list[int]
    crit_set: list[tuple[int, int]]
    theta: Fraction


def parse_solver_trace(data: dict[str, Any]) -> SolverTrace:
    """Parses `solver_trace.hpp`'s JSON (`write_trace_json`'s output,
    already `json.load`ed) into `SolverTrace`."""

    if data.get("version") != 1:
        raise ValueError(f"unsupported solver trace version: {data.get('version')!r}")

    rounds = [
        TraceRound(
            vertices=list(r["vertices"]),
            crit_set=[(u, v) for u, v in r["crit_set"]],
            theta=Fraction(*r["theta"]),
        )
        for r in data["rounds"]
    ]
    return SolverTrace(rounds=rounds)


def load_edge_list(path: str) -> nx.Graph:
    """Loads a graph from the `<n>\\n u v\\n...` edge-list format
    `cpp/examples/*.edges` uses (the same format `spt_mod`'s CLI reads).
    """

    g: nx.Graph = nx.Graph()
    with open(path) as f:
        n = int(f.readline())
        g.add_nodes_from(range(n))
        for line in f:
            line = line.strip()
            if not line:
                continue
            u, v = map(int, line.split())
            g.add_edge(u, v)
    return g


def _shrink_round(
    g: nx.Graph, vertices: list[int], crit_set: list[tuple[int, int]]
) -> tuple[nx.MultiGraph, list[tuple[int, int]]]:
    """
    Builds one round's shrunk multigraph (its pieces, contracted to
    points, with `crit_set` as edges) together with each shrunk edge's
    provenance back to the original graph's own vertex-id pair.

    The returned `shrunk_index_to_origuv` list is read back from `shrunk`
    immediately, in `shrunk.edges(data=True)`'s own traversal order --
    the same order `build_factored_pmf`'s internal edge tagging uses on
    (a copy of) this same graph, since copying a graph doesn't reorder
    its edges. That's what makes `LocalPiece.provenance`'s shrunk-level
    indices safe to use directly as indices into this list, regardless of
    what that traversal order actually is (e.g. not necessarily the same
    order `crit_set` itself lists edges in, once several of them connect
    the same pair of pieces).
    """

    h = g.subgraph(vertices)
    h_minus_crit: nx.Graph = nx.Graph(h)
    h_minus_crit.remove_edges_from(crit_set)

    piece_of: dict[int, int] = {}
    for idx, piece in enumerate(nx.connected_components(h_minus_crit)):
        for v in piece:
            piece_of[v] = idx

    shrunk: nx.MultiGraph = nx.MultiGraph()
    shrunk.add_nodes_from(range(len(set(piece_of.values()))))
    for u, v in crit_set:
        shrunk.add_edge(piece_of[u], piece_of[v], orig_uv=(u, v))

    shrunk_index_to_origuv = [data["orig_uv"] for _, _, data in shrunk.edges(data=True)]
    return shrunk, shrunk_index_to_origuv


def build_certificate(g: nx.Graph, trace: SolverTrace, verbose: bool = False) -> dict[str, Any]:
    """
    Builds a v4 certificate (`certificate_schema.json`) for `g` from its
    recorded solver `trace`. See the module docstring for the pipeline.

    Sanity-checks each round as it's built: `build_factored_pmf`'s own
    marginal should be uniformly the round's own recorded `theta` on
    every one of that round's shrunk edges -- the same check
    `scratch/nested_trace_validation.py` ran by hand on a real trace
    before this module existed. This is a build-time invariant of the
    deflation/pmf-construction math itself (mirroring `cunningham.hpp`'s
    own internal `assert(theta == ...)`), distinct from
    `validate_certificate`'s purely certificate-level checks below.
    """

    global_edges: list[tuple[int, int]] = []
    pieces_json: list[dict[str, Any]] = []

    for round_data in trace.rounds:
        shrunk, shrunk_index_to_origuv = _shrink_round(g, round_data.vertices, round_data.crit_set)

        base = len(global_edges)
        global_edges.extend(shrunk_index_to_origuv)

        factored = build_factored_pmf(shrunk, verbose=verbose)

        marginal = factored.marginal()
        assert all(v == round_data.theta for v in marginal), (
            f"round marginal {set(marginal)} isn't uniformly theta={round_data.theta}"
        )

        for piece in factored.pieces:
            piece_edges = sorted({base + j for j in piece.provenance})

            trees_json = []
            for entry in piece.result.support:
                tree_edges = sorted(
                    base + piece.provenance[local_i] for local_i, used in enumerate(entry.n) if used
                )
                w: Fraction = entry.weight
                trees_json.append({"edges": tree_edges, "weight": [w.numerator, w.denominator]})

            pieces_json.append(
                {
                    "edges": piece_edges,
                    "vertices": [str(v) for v in piece.graph.nodes],
                    "local_pmf": {"trees": trees_json},
                }
            )

    return {
        "certificate_version": 4,
        "graph": {
            "num_vertices": g.number_of_nodes(),
            "edges": [list(e) for e in global_edges],
        },
        "pieces": pieces_json,
    }


def validate_certificate(cert: dict[str, Any]) -> None:
    """
    Untrusted, purely certificate-level sanity checks -- everything a
    reader could confirm from `cert` alone, with no need for the trace or
    original graph that produced it. Catches builder bugs cheaply, long
    before a Lean run; not a substitute for the Lean proof (nothing here
    is trusted). Raises `AssertionError` on the first failure.
    """

    m = len(cert["graph"]["edges"])
    pieces = cert["pieces"]

    covered: set[int] = set()
    for i, piece in enumerate(pieces):
        edges = piece["edges"]
        piece_set = set(edges)
        assert len(piece_set) == len(edges), f"piece {i}: duplicate edge index within one piece"
        assert piece_set.isdisjoint(covered), f"piece {i}: edges overlap an earlier piece"
        covered |= piece_set

        trees = piece["local_pmf"]["trees"]
        total = Fraction(0)
        for t in trees:
            assert set(t["edges"]) <= piece_set, (
                f"piece {i}: a tree uses an edge outside its own piece"
            )
            num, den = t["weight"]
            w = Fraction(num, den)
            assert w >= 0, f"piece {i}: negative tree weight"
            total += w
        assert total == 1, f"piece {i}: tree weights sum to {total}, not 1"

    assert covered == set(range(m)), "pieces' edges don't partition the top-level edge list"
