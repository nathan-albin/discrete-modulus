/**
 * @file solver_trace.hpp
 * @brief Opt-in per-round trace recording for @ref spanning_tree_modulus,
 * and a versioned JSON writer for the recorded trace.
 *
 * The certificate builder (a planned, separate untrusted tool) needs the
 * sequence of `crit_set`s that Cunningham's algorithm dispatches, one per
 * round, together with the component each was carved from, in order to
 * reconstruct a pmf on spanning trees round by round. This header defines
 * that recorded shape (@ref SolverTrace) and its serialization
 * (@ref write_trace_json) independently of the algorithm itself, so
 * `spanning_tree_modulus` only needs to append one @ref TraceRound per
 * round when a caller opts in.
 */

#pragma once

#include <ostream>
#include <utility>
#include <vector>

#include <boost/rational.hpp>

#include "graphs.hpp"

namespace discrete_modulus {

using namespace boost;

/**
 * @brief One round of @ref spanning_tree_modulus's main loop: the
 * component it was carved from, the edge set dispatched at eta* = theta,
 * and theta itself.
 *
 * Vertex ids are the *original* input graph's vertex descriptors (mapped
 * back via `vertex_name`, the same way `spanning_tree_modulus` maps its
 * own `eta_star` results), not the round's local component numbering --
 * so a trace is self-contained and doesn't need the intermediate
 * component graphs to be replayed.
 */
struct TraceRound {
    rational<long> theta;
    std::vector<Vertex> vertices;                  ///< the component's vertex set
    std::vector<std::pair<Vertex, Vertex>> crit_set;  ///< the dispatched edges
};

/// The full recorded trace of a @ref spanning_tree_modulus run.
struct SolverTrace {
    std::vector<TraceRound> rounds;
};

/**
 * @brief Writes @p trace to @p os as versioned JSON (`"version": 1`).
 *
 * Every value is either an integer or an array of them, so this is a
 * plain hand-written emitter -- no JSON library dependency, no escaping
 * concerns (there are no free-form strings in the schema).
 */
inline void write_trace_json(std::ostream& os, const SolverTrace& trace) {
    os << "{\n  \"version\": 1,\n  \"rounds\": [\n";
    for (std::size_t r = 0; r < trace.rounds.size(); ++r) {
        const TraceRound& round = trace.rounds[r];

        os << "    {\n      \"vertices\": [";
        for (std::size_t i = 0; i < round.vertices.size(); ++i) {
            if (i > 0) {
                os << ", ";
            }
            os << round.vertices[i];
        }

        os << "],\n      \"crit_set\": [";
        for (std::size_t i = 0; i < round.crit_set.size(); ++i) {
            if (i > 0) {
                os << ", ";
            }
            os << "[" << round.crit_set[i].first << ", " << round.crit_set[i].second << "]";
        }

        os << "],\n      \"theta\": [" << round.theta.numerator() << ", " << round.theta.denominator() << "]\n";
        os << "    }" << (r + 1 < trace.rounds.size() ? ",\n" : "\n");
    }
    os << "  ]\n}\n";
}

}  // namespace discrete_modulus
