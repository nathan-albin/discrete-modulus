"""
Builds a certificate (schema version 5,
`docs/certification/certificate_schema.json`) from a C++ solver trace
(`solver_trace.hpp`) and the original input graph. See
`docs/certification/` for the full pipeline writeup and a worked example.

This is a standalone, untrusted, "elaborate freely" tool: bugs here
produce a certificate the Lean verifier rejects, not a false "verified"
result, so this module favors clarity over defensiveness in most places,
but still runs its own cheap sanity checks (`validate_certificate`)
before handing a certificate off, since those catch builder bugs long
before a Lean run would.

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
   this module was written.)
2. Shrink `h_k`'s pieces (its connected components after removing
   `crit_set`) to points, keeping `crit_set` as edges -- genuinely a
   `MultiGraph` in general (confirmed against a real multi-round trace to
   reach multiplicity up to 3 on `examples/nested`), which is exactly what
   `pmf_construction.build_factored_pmf` already expects.
3. Run `build_factored_pmf` on the shrunk multigraph (deflation +
   constructive tree packing per strictly-homogeneous piece, already
   implemented/tested).
4. Translate every piece's local edge indices into GLOBAL indices (into
   the certificate's own top-level `graph.edges` array), and append them
   to the certificate's flat `pieces` list -- **in reverse round order**
   (round 0's pieces last, the final round's pieces first), not the
   order rounds were recorded in. See `build_certificate`'s own docstring
   for why: round 0's crit_set runs between components later rounds
   themselves resolve, so round 0 depends on them, not the reverse of
   dispatch order.

Global edge indices are assigned round by round, in the order each
round's `crit_set` is recorded -- so the top-level `graph.edges` array is
built entirely from the trace itself, with no need to separately supply
or cross-check the original edge list's own ordering. This indexing is
independent of the `pieces` list's own (reversed) order -- edge index
assignment and piece emission order serve different purposes.

See `docs/certification/pipeline.md`'s certificate-builder section for
the validation results confirming steps 1-2 above against a real
multi-round solver trace.
"""

from __future__ import annotations

import json
import sys
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
    Builds a certificate (`certificate_schema.json`) for `g` from its
    recorded solver `trace`. See the module docstring for the pipeline.

    Sanity-checks each round as it's built: `build_factored_pmf`'s own
    marginal should be uniformly the round's own recorded `theta` on
    every one of that round's shrunk edges -- the same check confirmed by
    hand on a real trace before this module existed. This is a build-time
    invariant of the deflation/pmf-construction math itself (mirroring
    `cunningham.hpp`'s own internal `assert(theta == ...)`), distinct from
    `validate_certificate`'s purely certificate-level checks below.

    **Round order in `pieces` is reversed relative to `trace.rounds`.**
    The solver dispatches rounds outermost-first (round 0's crit_set is a
    tight set of the *whole* graph; round 1, round 2, ... recurse into
    whatever round 0's own crit_set-removal left as separate components),
    but the certificate's laminar-family fold (`PieceList` in
    `lean/DiscreteModulusCert/Glue.lean`) needs the opposite: a piece can
    only be verified once every piece its own contraction *depends on* has
    already been verified, and round 0's crit_set edges run *between*
    round 0's own leftover components -- exactly the components round 1,
    round 2, ... go on to resolve. So round 0 depends on round 1/round 2,
    not the other way around, the reverse of dispatch order. Confirmed by
    direct experiment against `examples/nested`'s real 3-round trace
    (forward order fails the maximality check on round 0's own piece;
    reversed order passes every piece). Within one round, core-before-
    rigid-base order (already `build_factored_pmf`'s own discovery order)
    is unaffected -- only the outer round-to-round grouping reverses,
    since a round's own within-round deflation already discovers pieces
    leaf-first (a core, self-contained, before the rigid base that
    depends on it).
    """

    global_edges: list[tuple[int, int]] = []
    round_pieces: list[list[dict[str, Any]]] = []

    for round_data in trace.rounds:
        shrunk, shrunk_index_to_origuv = _shrink_round(g, round_data.vertices, round_data.crit_set)

        base = len(global_edges)
        global_edges.extend(shrunk_index_to_origuv)

        factored = build_factored_pmf(shrunk, verbose=verbose)

        marginal = factored.marginal()
        assert all(v == round_data.theta for v in marginal), (
            f"round marginal {set(marginal)} isn't uniformly theta={round_data.theta}"
        )

        this_round_pieces: list[dict[str, Any]] = []
        for piece in factored.pieces:
            piece_edges = sorted({base + j for j in piece.provenance})

            trees_json = []
            for entry in piece.result.support:
                tree_edges = sorted(
                    base + piece.provenance[local_i] for local_i, used in enumerate(entry.n) if used
                )
                w: Fraction = entry.weight
                trees_json.append({"edges": tree_edges, "weight": [w.numerator, w.denominator]})

            this_round_pieces.append(
                {
                    "edges": piece_edges,
                    "vertices": [str(v) for v in piece.graph.nodes],
                    "local_pmf": {"trees": trees_json},
                }
            )
        round_pieces.append(this_round_pieces)

    pieces_json: list[dict[str, Any]] = [p for pieces in reversed(round_pieces) for p in pieces]

    eta = compute_eta_from_pieces(pieces_json, len(global_edges))
    rho = compute_rho(eta)

    return {
        "certificate_version": 5,
        "graph": {
            "num_vertices": g.number_of_nodes(),
            "edges": [list(e) for e in global_edges],
        },
        "pieces": pieces_json,
        "eta": [[f.numerator, f.denominator] for f in eta],
        "rho": [[f.numerator, f.denominator] for f in rho],
    }


def compute_eta_from_pieces(pieces: list[dict[str, Any]], m: int) -> list[Fraction]:
    """
    The optimal pmf's marginal at every edge (global index), computed
    directly from a certificate's own `pieces` -- summing each declared
    tree's weight into every edge it uses. This is the same per-piece
    composition `Pmf.glue_marginal`/`PieceList.glueAll_marginal`
    (`lean/DiscreteModulusCert/Glue.lean`) prove sound on the Lean side:
    linear in pieces x edges, never touching the glued pmf's own
    (exponential) support.
    """

    eta = [Fraction(0)] * m
    for piece in pieces:
        for t in piece["local_pmf"]["trees"]:
            w = Fraction(*t["weight"])
            for e in t["edges"]:
                eta[e] += w
    return eta


def compute_eta(cert: dict[str, Any]) -> list[Fraction]:
    """`compute_eta_from_pieces` against an already-built certificate dict."""

    return compute_eta_from_pieces(cert["pieces"], len(cert["graph"]["edges"]))


def compute_rho(eta: list[Fraction]) -> list[Fraction]:
    """rho = eta / ||eta||^2, the admissible density the Cauchy-Schwarz
    duality argument makes simultaneously optimal with eta (see
    `lean/DiscreteModulusCert/Optimality.lean`'s `certificate_optimality`
    for the formal statement and proof)."""

    norm_sq = sum((e * e for e in eta), Fraction(0))
    if norm_sq == 0:
        raise ValueError("sum of squared etas is zero; rho is undefined")
    return [e / norm_sq for e in eta]


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

    eta_check = compute_eta(cert)
    declared_eta = [Fraction(num, den) for num, den in cert["eta"]]
    assert len(declared_eta) == m, f"eta has {len(declared_eta)} entries, expected {m}"
    assert eta_check == declared_eta, "declared eta doesn't match pieces' own composed marginals"

    rho_check = compute_rho(eta_check)
    declared_rho = [Fraction(num, den) for num, den in cert["rho"]]
    assert len(declared_rho) == m, f"rho has {len(declared_rho)} entries, expected {m}"
    assert rho_check == declared_rho, "declared rho doesn't match eta / ||eta||^2"


def _dumps_compact(obj: Any, indent: int = 2) -> str:
    """
    Like `json.dumps(obj, indent=indent)`, except any list whose elements
    are all JSON primitives (int/float/str/bool/None) -- edge pairs, tree
    edge-index lists, `[num, den]` rationals -- is written inline via plain
    `json.dumps` instead of one element per line. Plain `indent=2` recurses
    into every nested list regardless of size, which turns something like
    `[20, 40]` into 4 lines; this keeps the certificate human-readable
    without losing the top-level object/array structure's indentation.
    """

    def is_leaf_list(x: Any) -> bool:
        return isinstance(x, list) and all(
            v is None or isinstance(v, (bool, int, float, str)) for v in x
        )

    def fmt(x: Any, level: int) -> str:
        pad = " " * (indent * level)
        pad_in = " " * (indent * (level + 1))
        if isinstance(x, dict):
            if not x:
                return "{}"
            items = [f"{pad_in}{json.dumps(k)}: {fmt(v, level + 1)}" for k, v in x.items()]
            return "{\n" + ",\n".join(items) + "\n" + pad + "}"
        if isinstance(x, list):
            if not x:
                return "[]"
            if is_leaf_list(x):
                return json.dumps(x)
            items = [f"{pad_in}{fmt(v, level + 1)}" for v in x]
            return "[\n" + ",\n".join(items) + "\n" + pad + "]"
        return json.dumps(x)

    return fmt(obj, 0)


def build_certificate_from_files(prefix: str) -> dict[str, Any]:
    """`build_certificate` from a `<prefix>.edges`/`<prefix>.trace.json`
    pair on disk -- the same pairing `spt_mod <prefix> --trace` produces."""

    g = load_edge_list(f"{prefix}.edges")
    with open(f"{prefix}.trace.json") as f:
        trace = parse_solver_trace(json.load(f))
    return build_certificate(g, trace)


def main(argv: list[str] | None = None) -> None:
    """
    `python -m discrete_modulus.certificate_builder <prefix>`: builds,
    validates, and writes `<prefix>.certificate.json`, matching `spt_mod`'s
    own `<prefix>` convention. Makes regenerating any checked-in
    `cpp/examples/*.certificate.json` a single, repeatable step rather than
    an untracked, one-off command.
    """

    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 1:
        print("usage: python -m discrete_modulus.certificate_builder <prefix>", file=sys.stderr)
        raise SystemExit(2)

    cert = build_certificate_from_files(argv[0])
    validate_certificate(cert)
    with open(f"{argv[0]}.certificate.json", "w") as f:
        f.write(_dumps_compact(cert))
        f.write("\n")


if __name__ == "__main__":
    main()
