/**
 * @file spt_mod.cpp
 * @brief Computes the spanning tree modulus of a graph.
 *
 * Usage:
 *     spt_mod <prefix>
 *
 * Loads the file "<prefix>.edges", which should have the following
 * format:
 *   - line 1: an integer, n, containing the number of vertices in the
 *     graph
 *   - line 2-?: a pair of integers "a b" indicating that vertex a is
 *     connected to vertex b
 *
 * Vertices are assumed to be numbered 0, 1, ..., n-1. Upon completion,
 * eta* is written to "<prefix>.eta", with rows "a b p q" indicating that
 * edge {a,b} has eta* value p/q.
 */

#include <fstream>
#include <iostream>
#include <string>

#include <discrete_modulus/cunningham.hpp>
#include <discrete_modulus/graphs.hpp>

using namespace discrete_modulus;

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "\nUsage:\n  " << argv[0] << " <prefix>\n\n";
        return 1;
    }

    std::string prefix = argv[1];

    int n, u, v;

    std::ifstream is(prefix + ".edges");
    if (!is) {
        std::cerr << "Could not open file " << prefix << ".edges\n";
        return 1;
    }
    is >> n;
    Graph g(n);
    while (is >> u >> v) {
        add_edge(u, v, g);
    }
    is.close();

    auto eta = spanning_tree_modulus(g, true);

    std::ofstream os(prefix + ".eta");
    EdgeIterator ei, ei_end;
    for (boost::tie(ei, ei_end) = edges(g); ei != ei_end; ++ei) {
        auto it = eta.find(*ei);
        os << source(*ei, g) << " " << target(*ei, g) << " " << it->second.numerator() << " "
           << it->second.denominator() << "\n";
    }
    os.close();

    return 0;
}
