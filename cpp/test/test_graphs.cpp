#include <catch2/catch_test_macros.hpp>

#include <discrete_modulus/graphs.hpp>

using namespace discrete_modulus;

TEST_CASE("complete_graph has the right vertex and edge counts", "[graphs]") {
    Graph g = complete_graph(5);
    REQUIRE(num_vertices(g) == 5);
    REQUIRE(num_edges(g) == 10);
}

TEST_CASE("cycle_plus_triangle has n+1 edges", "[graphs]") {
    Graph g = cycle_plus_triangle(6);
    REQUIRE(num_vertices(g) == 6);
    REQUIRE(num_edges(g) == 7);
}

TEST_CASE("disconnected_graph has two components", "[graphs]") {
    Graph g = disconnected_graph();
    auto comps = connected_component_graphs(g);
    REQUIRE(comps.size() == 2);
    for (const auto& c : comps) {
        REQUIRE(num_vertices(c) == 3);
        REQUIRE(num_edges(c) == 3);
    }
}

TEST_CASE("wheel_graph hub is connected to every rim vertex", "[graphs]") {
    Graph g = wheel_graph(6);
    REQUIRE(num_vertices(g) == 6);
    // 5 rim edges + 5 spokes
    REQUIRE(num_edges(g) == 10);
}

TEST_CASE("is_simple_graph accepts every demo graph", "[graphs]") {
    REQUIRE(is_simple_graph(complete_graph(5)));
    REQUIRE(is_simple_graph(cycle_plus_triangle(6)));
    REQUIRE(is_simple_graph(wheel_graph(6)));
    REQUIRE(is_simple_graph(disconnected_graph()));
    REQUIRE(is_simple_graph(growing_multipartite(4)));
    REQUIRE(is_simple_graph(complete_plus_triangle(5)));
}

TEST_CASE("is_simple_graph rejects a self-loop", "[graphs]") {
    Graph g(3);
    add_edge(0, 1, g);
    add_edge(1, 1, g);
    REQUIRE_FALSE(is_simple_graph(g));
}

TEST_CASE("is_simple_graph rejects parallel edges regardless of endpoint order", "[graphs]") {
    Graph g(3);
    add_edge(0, 1, g);
    add_edge(1, 0, g);
    REQUIRE_FALSE(is_simple_graph(g));
}
