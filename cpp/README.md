# discrete-modulus (C++)

Not implemented yet. This directory is a placeholder marking where a C++
reference implementation of the discrete modulus algorithms will eventually
live.

## Scope

This would be an **independent** reference implementation of the same
underlying theory covered by [`python/`](../python/) and the
[companion book](../book/) — not a wrapper or set of bindings around the
Python package. The point of having multiple language implementations is to
have each one stand on its own as a faithful, idiomatic implementation of
the algorithms, not to share code or runtime dependencies across languages.

## Intended layout

Expected to mirror `python/`'s shape once it exists:

- A CMake-built library (`include/`/`src/`, name TBD), implementing the
  same core algorithms (`matrix_modulus`/`modulus` and the family-of-objects
  functors) as `python/src/discrete_modulus/`.
- `test/`, using a standard C++ test framework (e.g. Catch2 or GoogleTest).
- `docs/`, an API reference built with
  [Doxygen](https://www.doxygen.nl/), analogous to how
  [`python/docs/`](../python/docs/) uses `quartodoc`.

## CI

`.github/workflows/book.yml` is already structured so that adding a C++
docs build is additive: a new `build-cpp-docs` job (rendering `cpp/docs/`
via Doxygen) plus one more download/copy step in the `deploy` job
(publishing it under `reference/cpp/`) — the existing book and Python jobs
wouldn't need to change.
