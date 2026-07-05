/**
 * @file graphs.hpp
 * @brief Graph/flow-graph type aliases, subgraph/component helpers, and
 * demo graph generators used by @ref cunningham.hpp.
 */

#pragma once

#include <cmath>
#include <map>
#include <random>
#include <vector>

#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/connected_components.hpp>
#include <boost/graph/filtered_graph.hpp>

namespace discrete_modulus {

// Confined to this namespace only, so downstream code that includes this
// header does not get `boost`'s names injected into its own namespace.
using namespace boost;

//----------------------------------------------------------------
// Main graph type
//----------------------------------------------------------------

/// Traits for @ref Graph.
using Traits = adjacency_list_traits<vecS, vecS, undirectedS>;

/**
 * @brief The undirected graph type used throughout this library.
 *
 * Vertices carry a `vertex_name` property (used to map a component's
 * local vertex descriptors back to the original graph's vertex
 * descriptors after splitting into connected components; see
 * @ref subgraph). Edges carry an `edge_index` (a stable 0..m-1 numbering)
 * and an `edge_weight` (used as the current point `x` in Cunningham's
 * algorithm; see cunningham.hpp).
 */
using Graph = adjacency_list<
    vecS, vecS, undirectedS, property<vertex_name_t, Traits::vertex_descriptor>,
    property<edge_index_t, int, property<edge_weight_t, long>>>;

using Vertex = graph_traits<Graph>::vertex_descriptor;
using Edge = graph_traits<Graph>::edge_descriptor;
using VertexIterator = graph_traits<Graph>::vertex_iterator;
using EdgeIterator = graph_traits<Graph>::edge_iterator;

//----------------------------------------------------------------
// Flow graph type
//----------------------------------------------------------------

/// Traits for @ref FlowGraph.
using FlowTraits = adjacency_list_traits<vecS, vecS, directedS>;
using FlowVertex = FlowTraits::vertex_descriptor;
using FlowEdge = FlowTraits::edge_descriptor;

/**
 * @brief The directed, capacitated graph type used for the max-flow
 * subproblem in Cunningham's algorithm (see `create_flow_graph` in
 * cunningham.hpp). `edge_reverse` records, for every directed edge, its
 * paired reverse-residual edge, as required by
 * `boost::push_relabel_max_flow`.
 */
using FlowGraph = adjacency_list<
    vecS, vecS, directedS, no_property,
    property<edge_capacity_t, long,
             property<edge_residual_capacity_t, long, property<edge_reverse_t, FlowTraits::edge_descriptor>>>>;

/**
 * @brief Builds the subgraph of @p g induced by the given vertices.
 *
 * The returned graph's `vertex_name` property maps each of its (local)
 * vertices back to the corresponding vertex descriptor in @p g, so that
 * results computed on the subgraph can be mapped back to @p g.
 */
template <typename G>
Graph subgraph(const G& g, std::vector<Vertex> v) {
    Graph sg;

    std::map<Vertex, Vertex> local_to_global;
    std::map<Vertex, Vertex> global_to_local;

    for (std::size_t i = 0; i < v.size(); ++i) {
        Vertex v_new = add_vertex(get(vertex_name, g, v[i]), sg);
        local_to_global.insert({v_new, v[i]});
        global_to_local.insert({v[i], v_new});
    }

    typename graph_traits<G>::vertex_iterator vi, vi_end;
    for (boost::tie(vi, vi_end) = vertices(sg); vi != vi_end; ++vi) {
        Vertex vv = local_to_global[*vi];
        typename graph_traits<G>::out_edge_iterator ei, ei_end;
        for (boost::tie(ei, ei_end) = out_edges(vv, g); ei != ei_end; ++ei) {
            Vertex uu = target(*ei, g);
            auto u = global_to_local.find(uu);
            if (u != global_to_local.end() && !edge(*vi, u->second, sg).second) {
                add_edge(*vi, u->second, sg);
            }
        }
    }

    return sg;
}

/// Splits @p g into one @ref Graph per connected component.
template <typename G>
std::vector<Graph> connected_component_graphs(const G& g) {
    std::vector<Graph> components;

    std::vector<int> component(num_vertices(g));
    int num_components = connected_components(g, &component[0]);

    std::vector<std::vector<Vertex>> component_v(num_components);
    int i = 0;
    typename graph_traits<G>::vertex_iterator vi, vi_end;
    for (boost::tie(vi, vi_end) = vertices(g); vi != vi_end; ++vi, ++i) {
        component_v[component[i]].push_back(*vi);
    }

    for (const auto& vs : component_v) {
        components.push_back(subgraph(g, vs));
    }

    return components;
}

/// Edge filter selecting edges *not* in a given critical/tight set.
struct NonCriticalEdge {
    NonCriticalEdge() = default;
    explicit NonCriticalEdge(std::set<Edge> a) : m_A(std::move(a)) {}
    bool operator()(const Edge& e) const { return m_A.count(e) == 0; }
    std::set<Edge> m_A;
};

/**
 * @brief Splits @p g into connected components after removing the
 * critical edge set @p A.
 */
inline std::vector<Graph> induced_components(Graph& g, const std::set<Edge>& A) {
    NonCriticalEdge filter(A);
    filtered_graph<Graph, NonCriticalEdge> fg(g, filter);
    return connected_component_graphs(fg);
}

//----------------------------------------------------------------
// Demo graphs
//----------------------------------------------------------------

/// A cycle on @p n vertices plus one extra chord (between vertices 1 and n-1).
inline Graph cycle_plus_triangle(int n) {
    Graph g(n);
    for (int i = 0; i < n; ++i) {
        add_edge(i, (i + 1) % n, g);
    }
    add_edge(1, n - 1, g);
    return g;
}

/// The complete graph on @p n vertices.
inline Graph complete_graph(int n) {
    Graph g(n);
    for (int i = 0; i < n - 1; ++i) {
        for (int j = i + 1; j < n; ++j) {
            add_edge(i, j, g);
        }
    }
    return g;
}

/// The wheel graph: a cycle on n-1 vertices plus one hub vertex n-1.
inline Graph wheel_graph(int n) {
    Graph g(n);
    for (int i = 0; i < n - 1; ++i) {
        add_edge(i, (i + 1) % (n - 1), g);
        add_edge(i, n - 1, g);
    }
    return g;
}

/**
 * @brief A multipartite graph with growing layer sizes (1, 2, ..., n_layers)
 * and complete bipartite connections between consecutive layers.
 */
inline Graph growing_multipartite(int n_layers) {
    const int n = (n_layers * (n_layers + 1)) / 2;
    Graph g(n);

    int offset = 0;
    for (int i = 1; i < n_layers; ++i) {
        int prev_offset = offset;
        offset += i;
        for (int src_i = 0; src_i < i + 1; ++src_i) {
            for (int tgt_i = 0; tgt_i < i; ++tgt_i) {
                add_edge(src_i + offset, tgt_i + prev_offset, g);
            }
        }
    }

    return g;
}

/// The complete graph on n-1 vertices, plus one extra vertex attached to two of them.
inline Graph complete_plus_triangle(int n) {
    Graph g(n);
    for (int i = 0; i < n - 2; ++i) {
        for (int j = i + 1; j < n - 1; ++j) {
            add_edge(i + 1, j + 1, g);
        }
    }
    add_edge(0, 1, g);
    add_edge(0, 2, g);
    return g;
}

/// @p g with vertices relabeled according to @p perm.
inline Graph permuted_graph(const Graph& g, const std::vector<int>& perm) {
    int n = num_vertices(g);
    Graph pg(n);

    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        Vertex u = perm[source(*ei, g)], v = perm[target(*ei, g)];
        add_edge(u, v, pg);
    }

    return pg;
}

/// Two disjoint triangles: a minimal example of a disconnected graph.
inline Graph disconnected_graph() {
    Graph g(6);
    add_edge(0, 1, g);
    add_edge(1, 2, g);
    add_edge(2, 0, g);
    add_edge(3, 4, g);
    add_edge(4, 5, g);
    add_edge(5, 3, g);
    return g;
}

/// An Erdos-Renyi G(n,p) random graph.
inline Graph random_gnp_graph(int n, double p, int seed) {
    std::default_random_engine rg(seed);
    Graph g(n);

    std::uniform_real_distribution<double> distribution(0.0, 1.0);
    for (int i = 0; i < n - 1; ++i) {
        for (int j = i + 1; j < n; ++j) {
            if (distribution(rg) < p) {
                add_edge(i, j, g);
            }
        }
    }

    return g;
}

/// A random geometric graph: n uniform points in the unit square, connected within radius r.
inline Graph random_geometric_graph(int n, double r, int seed = 381928) {
    std::default_random_engine rg(seed);
    Graph g(n);

    std::uniform_real_distribution<double> distribution(0.0, 1.0);
    std::vector<double> x(n), y(n);
    for (int i = 0; i < n; ++i) {
        x[i] = distribution(rg);
        y[i] = distribution(rg);
    }

    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            double d = std::sqrt((x[i] - x[j]) * (x[i] - x[j]) + (y[i] - y[j]) * (y[i] - y[j]));
            if (d < r) {
                add_edge(i, j, g);
            }
        }
    }

    return g;
}

}  // namespace discrete_modulus
