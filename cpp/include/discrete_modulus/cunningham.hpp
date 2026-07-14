/**
 * @file cunningham.hpp
 * @brief Exact spanning tree modulus via Cunningham's algorithm.
 *
 * Implements the algorithm of Albin, Kottegoda, and Poggi-Corradini, "An
 * Exact-Arithmetic Algorithm for Spanning Tree Modulus," Networks 85(4),
 * 412-424, which builds on Cunningham's matroid-greedy algorithm for
 * polymatroid bases. See the Python package's
 * `discrete_modulus.spanning_tree_modulus` module and the companion
 * book's "Exact Spanning Tree Modulus" chapter for the underlying theory
 * (rank, polymatroids, polymatroid bases, the max-flow subproblem, the
 * integer-arithmetic reformulation, graph vulnerability, and computing
 * modulus by repeatedly extracting tight sets).
 *
 * This is an independent C++ implementation, not a port bound to the
 * Python package's exact internal structure -- but it deliberately
 * mirrors its public shape (`create_flow_graph`, `cunningham_min`,
 * `graph_vulnerability`, `spanning_tree_modulus`) and drops the
 * performance-variant flags of the original research code in favor of a
 * single algorithm path, for clarity and cross-language verifiability.
 *
 * One optimization from the original *is* kept: since a component
 * produced by splitting on a tight set can never have a larger
 * vulnerability than the component it was split from,
 * `spanning_tree_modulus` passes each child component's parent's theta
 * down as an upper bound to `graph_vulnerability`, restricting its binary
 * search range. Dropping this (as an earlier version of this file did)
 * measurably matters: on `examples/random.edges`, which decomposes into
 * many components, the unrestricted search never finished in a
 * reasonable time.
 */

#pragma once

#include <algorithm>
#include <cassert>
#include <iomanip>
#include <iostream>
#include <map>
#include <set>
#include <utility>
#include <vector>

#include <boost/graph/push_relabel_max_flow.hpp>
#include <boost/rational.hpp>

#include "graphs.hpp"
#include "solver_trace.hpp"

namespace discrete_modulus {

using namespace boost;

/**
 * @brief The reusable max-flow network for @ref cunningham_min /
 * @ref graph_vulnerability / @ref spanning_tree_modulus, built once per
 * graph by @ref create_flow_graph.
 *
 * Bundles the flow graph together with handles to the specific edges
 * whose capacities get updated on every call (looked up once here, since
 * `FlowGraph` has parallel edges between some vertex pairs -- see
 * `create_flow_graph`'s implementation comments).
 */
struct FlowContext {
    FlowGraph graph;
    FlowVertex src{};
    FlowVertex tgt{};
    std::vector<FlowEdge> forward;      ///< indexed by edge_index: source(e,g) -> target(e,g)
    std::vector<FlowEdge> backward;     ///< indexed by edge_index: target(e,g) -> source(e,g)
    std::vector<FlowEdge> to_target;    ///< indexed by vertex: v -> target
    std::vector<FlowEdge> from_source;  ///< indexed by vertex: source -> v
};

namespace detail {

/**
 * @brief Adds a directed capacity edge @p u -> @p v to @p fg, along with
 * its required zero-capacity reverse-residual companion @p v -> @p u.
 *
 * `boost::push_relabel_max_flow` requires every "real" capacity edge to
 * have its own dedicated reverse companion. Representing an undirected
 * edge's capacity (which should be usable in *either* direction)
 * therefore takes two calls to this function -- one per direction --
 * i.e. 4 underlying `FlowGraph` edges in total, not 2.
 */
inline FlowEdge add_capacity_edge(FlowGraph& fg, FlowVertex u, FlowVertex v, long capacity) {
    FlowEdge fe = add_edge(u, v, fg).first;
    FlowEdge fe_r = add_edge(v, u, fg).first;
    put(edge_capacity, fg, fe, capacity);
    put(edge_capacity, fg, fe_r, 0);
    put(edge_reverse, fg, fe, fe_r);
    put(edge_reverse, fg, fe_r, fe);
    return fe;
}

/**
 * @brief One max-flow step of Cunningham's algorithm: how far can `x` be
 * increased on edge @p e without leaving the polymatroid `P(qf)`?
 *
 * @param g Graph whose `edge_weight` property map holds the current `x`.
 * @param ctx Reusable flow network for @p g, from @ref create_flow_graph.
 * @param e The edge being incremented.
 * @param q See the module-level (file) documentation.
 * @return `{eps, crit_edges}`: the maximum amount `x(e)` can be
 * increased, and the critical (tight) edge set found by the min cut.
 */
inline std::pair<long, std::set<Edge>> solve_subproblem(Graph& g, FlowContext& ctx, const Edge& e, long q) {
    const long n = static_cast<long>(num_vertices(g));
    Vertex u = source(e, g), v = target(e, g);

    // capacities between "regular" nodes
    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        int idx = get(edge_index, g, *ei);
        long w = get(edge_weight, g, *ei);
        put(edge_capacity, ctx.graph, ctx.forward[idx], w);
        put(edge_capacity, ctx.graph, ctx.backward[idx], w);
    }

    // fixed capacities to the target
    VertexIterator vi, vi_end;
    for (boost::tie(vi, vi_end) = vertices(g); vi != vi_end; ++vi) {
        put(edge_capacity, ctx.graph, ctx.to_target[*vi], 2 * q);
    }

    // capacities from the source. Vertices incident to e get an
    // "unlimited" capacity so the min cut never has to pass through
    // them; the total capacity into the target is 2*q*n, so anything
    // larger than that can never be the bottleneck. Using a finite bound
    // (rather than an arbitrary huge constant) keeps everything well
    // inside `long` range.
    const long unlimited = 2 * q * n + 1;
    for (boost::tie(vi, vi_end) = vertices(g); vi != vi_end; ++vi) {
        long capacity;
        if (*vi == u || *vi == v) {
            capacity = unlimited;
        } else {
            capacity = 0;
            graph_traits<Graph>::out_edge_iterator oei, oei_end;
            for (boost::tie(oei, oei_end) = out_edges(*vi, g); oei != oei_end; ++oei) {
                capacity += get(edge_weight, g, *oei);
            }
        }
        put(edge_capacity, ctx.graph, ctx.from_source[*vi], capacity);
    }

    // run max flow
    long flow = push_relabel_max_flow(ctx.graph, ctx.src, ctx.tgt);
    assert(flow % 2 == 0);

    long eps = flow / 2 - q;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        eps -= get(edge_weight, g, *ei);
    }

    // the critical set is made of the vertices reachable from the source
    // via positive-residual-capacity edges
    std::set<Vertex> C;
    std::vector<FlowVertex> process{ctx.src};
    while (!process.empty()) {
        FlowVertex w = process.back();
        process.pop_back();
        C.insert(static_cast<Vertex>(w));

        graph_traits<FlowGraph>::out_edge_iterator fei, fei_end;
        for (boost::tie(fei, fei_end) = out_edges(w, ctx.graph); fei != fei_end; ++fei) {
            if (get(edge_residual_capacity, ctx.graph, *fei) > 0) {
                FlowVertex w2 = target(*fei, ctx.graph);
                if (C.count(static_cast<Vertex>(w2)) == 0) {
                    process.push_back(w2);
                }
            }
        }
    }
    C.erase(static_cast<Vertex>(ctx.src));

    std::set<Edge> crit_edges;
    for (Vertex a : C) {
        graph_traits<Graph>::out_edge_iterator oei, oei_end;
        for (boost::tie(oei, oei_end) = out_edges(a, g); oei != oei_end; ++oei) {
            if (C.count(target(*oei, g)) > 0) {
                crit_edges.insert(*oei);
            }
        }
    }

    return {eps, crit_edges};
}

}  // namespace detail

/**
 * @brief Builds the reusable max-flow network for @p g.
 *
 * @pre @p g outlives, and is not modified (beyond its `edge_weight`
 * property, which @ref cunningham_min manages) for the lifetime of, the
 * returned `FlowContext` -- it assigns and relies on a stable
 * `edge_index` numbering of @p g's edges.
 */
inline FlowContext create_flow_graph(Graph& g) {
    const long n = static_cast<long>(num_vertices(g));

    FlowContext ctx;
    ctx.graph = FlowGraph(static_cast<std::size_t>(n + 2));
    ctx.src = static_cast<FlowVertex>(n);
    ctx.tgt = static_cast<FlowVertex>(n + 1);

    const std::size_t m = num_edges(g);
    ctx.forward.resize(m);
    ctx.backward.resize(m);
    ctx.to_target.resize(static_cast<std::size_t>(n));
    ctx.from_source.resize(static_cast<std::size_t>(n));

    std::size_t i = 0;
    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei, ++i) {
        put(edge_index, g, *ei, static_cast<int>(i));
        Vertex u = source(*ei, g), v = target(*ei, g);
        ctx.forward[i] = detail::add_capacity_edge(ctx.graph, u, v, 0);
        ctx.backward[i] = detail::add_capacity_edge(ctx.graph, v, u, 0);
    }

    VertexIterator vi, vi_end;
    for (boost::tie(vi, vi_end) = vertices(g); vi != vi_end; ++vi) {
        ctx.to_target[*vi] = detail::add_capacity_edge(ctx.graph, *vi, ctx.tgt, 0);
        ctx.from_source[*vi] = detail::add_capacity_edge(ctx.graph, ctx.src, *vi, 0);
    }

    return ctx;
}

/**
 * @brief Finds a P(qf)-basis for the constant function @p p, along with
 * a tight set, using Cunningham's greedy algorithm.
 *
 * @param g Graph to compute on; its `edge_weight` property map is used
 * to store the current point `x` and is reset to zero at the start of
 * this call.
 * @param ctx Reusable flow network for @p g, from @ref create_flow_graph.
 * @param p,q Together, `p/q` is the rational constant whose P(f)-basis
 * is being sought.
 * @return `{x(E), A}`: the total weight of the P(qf)-basis found (`x`
 * itself is left in @p g's `edge_weight` property map), and a tight set
 * `A` for it (i.e. `x(A) == q * f(A)`).
 */
inline std::pair<long, std::set<Edge>> cunningham_min(Graph& g, FlowContext& ctx, long p, long q) {
    std::set<Edge> A;

    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        put(edge_weight, g, *ei, 0);
    }

    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        if (A.count(*ei) > 0) {
            continue;
        }

        auto [eps, crit_edges] = detail::solve_subproblem(g, ctx, *ei, q);

        long w = get(edge_weight, g, *ei);
        if (eps < p - w) {
            A.insert(crit_edges.begin(), crit_edges.end());
        } else {
            eps = p - w;
        }
        put(edge_weight, g, *ei, w + eps);
    }

    long total = 0;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        total += get(edge_weight, g, *ei);
    }

    return {total, A};
}

/**
 * @brief Finds the vulnerability theta(G) of a graph by binary search,
 * along with an optimal tight set.
 *
 * @param g Graph to compute on.
 * @param ctx Reusable flow network for @p g, from @ref create_flow_graph.
 * @param ubound An upper bound on theta(G), when known (e.g. the parent
 * component's own theta, during `spanning_tree_modulus`'s recursive
 * decomposition) -- restricts the binary search range. Defaults to 1,
 * theta's global maximum possible value.
 * @return `{theta, J}`: the vulnerability of @p g, and a tight edge set
 * achieving it.
 */
inline std::pair<rational<long>, std::set<Edge>> graph_vulnerability(
    Graph& g, FlowContext& ctx, rational<long> ubound = rational<long>(1, 1)) {
    const long m = static_cast<long>(num_edges(g));
    const long n = static_cast<long>(num_vertices(g));

    std::set<rational<long>> theta_set;
    for (long q = 1; q <= m; ++q) {
        for (long p = 1; p <= std::min(n - 1, q); ++p) {
            rational<long> val(p, q);
            if (val <= ubound) {
                theta_set.insert(val);
            }
        }
    }
    std::vector<rational<long>> Theta(theta_set.begin(), theta_set.end());

    std::set<Edge> crit_set;
    std::size_t lb = 0, ub = Theta.size();

    while (lb < ub) {
        std::size_t mid = (ub + lb) / 2;
        long p = Theta[mid].numerator(), q = Theta[mid].denominator();

        auto [xE, J] = cunningham_min(g, ctx, p, q);

        if (xE >= q * (n - 1)) {
            ub = mid;
            crit_set = J;
        } else {
            lb = mid + 1;
        }
    }

    return {Theta[lb], crit_set};
}

/**
 * @brief Computes the exact spanning tree modulus of @p g using
 * Cunningham's algorithm.
 *
 * @param g Graph to compute on.
 * @param verbose If true, prints a progress table to stdout as edges are
 * assigned their eta* value.
 * @param trace If non-null, appends one @ref TraceRound per round of the
 * main loop below (opt-in; leaving this null, the default, reproduces the
 * exact behavior of every existing caller).
 * @return eta*: the exact spanning tree modulus edge weighting, whose
 * blocking dual is Chopra's family of feasible partitions (see the
 * companion book's "Exact Spanning Tree Modulus" chapter).
 */
inline std::map<Edge, rational<long>> spanning_tree_modulus(Graph& g, bool verbose = false,
                                                              SolverTrace* trace = nullptr) {
    std::map<Edge, rational<long>> eta_star;
    long remain = static_cast<long>(num_edges(g));

    // memorize vertex names so results from subgraphs (after splitting
    // into connected components) can be mapped back to g
    VertexIterator vi, vi_end;
    for (boost::tie(vi, vi_end) = vertices(g); vi != vi_end; ++vi) {
        put(vertex_name, g, *vi, *vi);
    }

    // each entry pairs a component with an upper bound on its own theta
    // (inherited from the component it was split from, since splitting
    // can never increase vulnerability) -- restricting graph_vulnerability's
    // search range this way matters a great deal on inputs that
    // decompose into many components (see the file-level docs above)
    std::vector<std::pair<Graph, rational<long>>> process;
    for (auto& comp : connected_component_graphs(g)) {
        process.emplace_back(std::move(comp), rational<long>(1, 1));
    }

    if (verbose) {
        std::cout << "| " << std::setw(12) << "eta" << " | " << std::setw(12) << "num edge" << " | "
                  << std::setw(12) << "edge_remain" << " | " << std::setw(12) << "comp remain" << " |" << std::endl;
    }

    while (!process.empty()) {
        Graph h = std::move(process.back().first);
        rational<long> parent_theta = process.back().second;
        process.pop_back();

        if (num_edges(h) == 0) {
            continue;
        }

        FlowContext ctx = create_flow_graph(h);
        auto [theta, J] = graph_vulnerability(h, ctx, parent_theta);

        const long m = static_cast<long>(num_edges(h));
        long p = theta.numerator(), q = theta.denominator();
        if (static_cast<long>(J.size()) == m) {
            // the whole edge set came back tight; rerun with a slightly
            // smaller p/q so the complement isn't empty
            long pp = p * m * m - q;
            long qq = q * m * m;
            J = cunningham_min(h, ctx, pp, qq).second;
        }

        // complement of the tight set: these edges get eta* = theta
        std::set<Edge> crit_set;
        EdgeIterator ei, ei_end;
        for (boost::tie(ei, ei_end) = edges(h); ei != ei_end; ++ei) {
            if (J.count(*ei) == 0) {
                crit_set.insert(*ei);
            }
        }

        TraceRound trace_round;
        if (trace != nullptr) {
            VertexIterator hvi, hvi_end;
            for (boost::tie(hvi, hvi_end) = vertices(h); hvi != hvi_end; ++hvi) {
                trace_round.vertices.push_back(get(vertex_name, h, *hvi));
            }
            trace_round.theta = theta;
        }

        for (const Edge& e : crit_set) {
            Vertex uu = get(vertex_name, h, source(e, h));
            Vertex vv = get(vertex_name, h, target(e, h));
            eta_star[edge(uu, vv, g).first] = theta;
            if (trace != nullptr) {
                trace_round.crit_set.emplace_back(uu, vv);
            }
        }

        if (trace != nullptr) {
            trace->rounds.push_back(std::move(trace_round));
        }

        // split into connected components after removing crit_set (via a
        // non-mutating filtered view -- removing edges one at a time
        // from a vecS-based adjacency_list can invalidate other stored
        // edge descriptors, so h itself is never modified)
        std::vector<Graph> comps = induced_components(h, crit_set);
        assert(theta == rational<long>(static_cast<long>(comps.size()) - 1, static_cast<long>(crit_set.size())));

        for (auto& comp : comps) {
            process.emplace_back(std::move(comp), theta);
        }

        remain -= static_cast<long>(crit_set.size());
        if (verbose) {
            std::cout << "| " << std::setw(12) << theta << " | " << std::setw(12) << crit_set.size() << " | "
                      << std::setw(12) << remain << " | " << std::setw(12) << process.size() << " |" << std::endl;
        }
    }

    return eta_star;
}

}  // namespace discrete_modulus
