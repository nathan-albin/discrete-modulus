#include <fstream>
#include <map>
#include <sstream>
#include <string>

#include <catch2/catch_test_macros.hpp>

#include <discrete_modulus/cunningham.hpp>
#include <discrete_modulus/graphs.hpp>
#include <discrete_modulus/solver_trace.hpp>

using namespace discrete_modulus;

namespace {

// Mirrors spt_mod.cpp's ".edges" parsing.
Graph load_edges(const std::string& path) {
    std::ifstream is(path);
    REQUIRE(is);

    int n, u, v;
    is >> n;
    Graph g(n);
    while (is >> u >> v) {
        add_edge(u, v, g);
    }
    return g;
}

// Replays a trace the way the certificate builder will: every edge in a
// round's crit_set gets eta* = that round's theta.
std::map<Edge, rational<long>> eta_from_trace(const Graph& g, const SolverTrace& trace) {
    std::map<Edge, rational<long>> eta;
    for (const auto& round : trace.rounds) {
        for (const auto& [u, v] : round.crit_set) {
            eta[edge(u, v, g).first] = round.theta;
        }
    }
    return eta;
}

void check_round_trip(const std::string& edges_path) {
    Graph g = load_edges(edges_path);

    SolverTrace trace;
    auto eta_direct = spanning_tree_modulus(g, false, &trace);
    auto eta_replayed = eta_from_trace(g, trace);

    REQUIRE(eta_replayed.size() == eta_direct.size());
    for (const auto& [e, val] : eta_direct) {
        auto it = eta_replayed.find(e);
        REQUIRE(it != eta_replayed.end());
        REQUIRE(it->second == val);
    }
}

}  // namespace

TEST_CASE("solver trace is a no-op for existing callers", "[solver_trace]") {
    Graph g = load_edges(std::string(DISCRETE_MODULUS_EXAMPLES_DIR) + "/house.edges");
    auto eta = spanning_tree_modulus(g);
    REQUIRE(eta.size() == num_edges(g));
}

TEST_CASE("solver trace replay reproduces eta* on house", "[solver_trace]") {
    check_round_trip(std::string(DISCRETE_MODULUS_EXAMPLES_DIR) + "/house.edges");
}

TEST_CASE("solver trace replay reproduces eta* on nested", "[solver_trace]") {
    check_round_trip(std::string(DISCRETE_MODULUS_EXAMPLES_DIR) + "/nested.edges");
}

TEST_CASE("write_trace_json produces the expected JSON for a single-round trace", "[solver_trace]") {
    // Matches the real house-graph run: one round, all 6 edges, theta = 2/3.
    SolverTrace trace;
    TraceRound round;
    round.theta = rational<long>(2, 3);
    round.vertices = {0, 1, 2, 3, 4};
    round.crit_set = {{0, 1}, {1, 2}, {2, 3}, {3, 4}, {0, 4}, {1, 4}};
    trace.rounds.push_back(round);

    std::ostringstream os;
    write_trace_json(os, trace);

    std::string expected =
        "{\n"
        "  \"version\": 1,\n"
        "  \"rounds\": [\n"
        "    {\n"
        "      \"vertices\": [0, 1, 2, 3, 4],\n"
        "      \"crit_set\": [[0, 1], [1, 2], [2, 3], [3, 4], [0, 4], [1, 4]],\n"
        "      \"theta\": [2, 3]\n"
        "    }\n"
        "  ]\n"
        "}\n";
    REQUIRE(os.str() == expected);
}
