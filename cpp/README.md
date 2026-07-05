# discrete-modulus (C++)

A C++ reference implementation of exact spanning tree modulus, computed via
Cunningham's algorithm — the algorithm of Albin, Kottegoda, and
Poggi-Corradini, "An Exact-Arithmetic Algorithm for Spanning Tree Modulus,"
Networks 85(4), 412-424. See the Python package's
[`discrete_modulus.spanning_tree_modulus`](../python/src/discrete_modulus/spanning_tree_modulus.py)
module and the companion book's
["Exact Spanning Tree Modulus"](../book/Exact_Spanning_Tree_Modulus.qmd)
chapter for the underlying theory.

## Scope

This is an **independent** reference implementation of the same underlying
theory covered by [`python/`](../python/) and the
[companion book](../book/) — not a wrapper or set of bindings around the
Python package. It mirrors the Python module's public shape
(`create_flow_graph`, `cunningham_min`, `graph_vulnerability`,
`spanning_tree_modulus`) where that made sense, but is otherwise a fresh,
idiomatic C++/Boost.Graph implementation, not a line-for-line port.

Only the exact spanning-tree-modulus algorithm is implemented here so far
— unlike `python/`, this does not (yet) have a C++ equivalent of
`algorithms.py`'s general `matrix_modulus`/`modulus` framework or the
family-of-objects functors.

## Layout

- `include/discrete_modulus/` — the header-only library:
  - `graphs.hpp` — the `Graph`/`FlowGraph` type aliases, subgraph/component
    helpers, and demo graph generators.
  - `cunningham.hpp` — the algorithm itself.
- `src/spt_mod.cpp` — a CLI: `spt_mod <prefix>` reads `<prefix>.edges` and
  writes `<prefix>.eta`.
- `examples/` — sample graphs for the CLI (`house`, `nested`, `random`,
  `celegans`, in increasing order of size/runtime — with a `Release`
  build, `random` takes well under a minute, but `celegans` takes a few
  minutes).
- `test/` — the Catch2 test suite.
- `docs/Doxyfile` — Doxygen config for the API reference.

## Building

Requires CMake >= 3.20, a C++17 compiler, and Boost >= 1.74 (the `graph`
component). On Debian/Ubuntu: `sudo apt install cmake libboost-graph-dev`
(already present in the devcontainer image).

```sh
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build
```

This builds the `spt_mod` CLI and the test suite (set
`-DDISCRETE_MODULUS_BUILD_TESTS=OFF` to skip the latter).

`-DCMAKE_BUILD_TYPE=Release` matters here more than it might for other
projects: this is a CPU-bound combinatorial algorithm, and an unoptimized
(default/`Debug`) build is dramatically slower — enough to make the
larger bundled examples (`random`, `celegans`) impractically slow.

## Running the tests

```sh
ctest --test-dir build --output-on-failure
```

## Running the CLI

```sh
./build/spt_mod examples/house
cat examples/house.eta
```

writes `examples/house.eta` (already checked into this repo, so this is a
quick way to confirm the build reproduces the recorded output).

## Building the API reference

Requires [Doxygen](https://www.doxygen.nl/) (and, optionally,
[Graphviz](https://graphviz.org/) for diagrams). From `docs/`:

```sh
doxygen Doxyfile
```

generates `docs/_site/html/`.

## CI

- `.github/workflows/cpp-test.yml` — builds and runs the test suite on
  every change under `cpp/`.
- `.github/workflows/book.yml`'s `build-cpp-docs` job renders this API
  reference and publishes it alongside the book and the Python API
  reference, under `reference/cpp/`.
