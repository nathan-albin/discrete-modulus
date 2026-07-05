#include <fstream>
#include <sstream>

#include <catch2/catch_test_macros.hpp>

#include <discrete_modulus/cunningham.hpp>
#include <discrete_modulus/graphs.hpp>

using namespace discrete_modulus;

TEST_CASE("notebook worked example: 6-cycle plus one chord", "[cunningham]") {
    Graph g(6);
    add_edge(0, 1, g);
    add_edge(1, 2, g);
    add_edge(2, 3, g);
    add_edge(3, 4, g);
    add_edge(4, 5, g);
    add_edge(5, 0, g);
    add_edge(0, 2, g);

    FlowContext ctx = create_flow_graph(g);
    auto [total, tight] = cunningham_min(g, ctx, 3, 4);

    // the triangle {0, 1, 2} is the tight set: exactly one of its three
    // edges gets shorted to 2 (the specific edge is greedy-order
    // dependent -- NetworkX's node-adjacency edge order hits a different
    // one of the three than Boost's does -- but every non-triangle edge
    // reaches 3, and the triangle's total is capped at 8 = q * rank(J)).
    int num_short = 0;
    long triangle_total = 0;
    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        Vertex u = source(*ei, g), v = target(*ei, g);
        long w = get(edge_weight, g, *ei);
        bool in_triangle = (u < 3 && v < 3);
        if (in_triangle) {
            triangle_total += w;
            if (w == 2) {
                ++num_short;
            } else {
                REQUIRE(w == 3);
            }
        } else {
            REQUIRE(w == 3);
        }
    }
    REQUIRE(num_short == 1);
    REQUIRE(triangle_total == 8);

    // the triangle {0, 1, 2} is the tight set
    REQUIRE(tight.size() == 3);

    auto [theta, J] = graph_vulnerability(g, ctx);
    REQUIRE(theta == rational<long>(3, 4));
}

TEST_CASE("complete_graph eta* is 2/n on every edge", "[cunningham]") {
    for (int n = 3; n <= 7; ++n) {
        Graph g = complete_graph(n);
        auto eta = spanning_tree_modulus(g);

        REQUIRE(eta.size() == num_edges(g));
        for (const auto& [e, val] : eta) {
            REQUIRE(val == rational<long>(2, n));
        }
    }
}

TEST_CASE("house graph matches the bundled house.eta fixture", "[cunningham]") {
    // 5-cycle plus chord (1,4) -- see cpp/examples/house.edges
    Graph g(5);
    add_edge(0, 1, g);
    add_edge(1, 2, g);
    add_edge(2, 3, g);
    add_edge(3, 4, g);
    add_edge(4, 0, g);
    add_edge(1, 4, g);

    auto eta = spanning_tree_modulus(g);

    REQUIRE(eta.size() == num_edges(g));
    for (const auto& [e, val] : eta) {
        REQUIRE(val == rational<long>(2, 3));
    }
}

TEST_CASE("disconnected graph matches per-component computation", "[cunningham]") {
    Graph g(6);
    add_edge(0, 1, g);
    add_edge(1, 2, g);
    add_edge(2, 0, g);
    add_edge(3, 4, g);
    add_edge(4, 5, g);
    add_edge(5, 3, g);

    auto eta = spanning_tree_modulus(g);

    REQUIRE(eta.size() == num_edges(g));
    for (const auto& [e, val] : eta) {
        REQUIRE(val == rational<long>(2, 3));
    }
}
