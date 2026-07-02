# discrete-modulus (Julia)

Not implemented yet. This directory is a placeholder marking where a Julia
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

- A `Project.toml`/`src/` package (name TBD), implementing the same core
  algorithms (`matrix_modulus`/`modulus` and the family-of-objects
  functors) as `python/src/discrete_modulus/`.
- `test/`, using Julia's built-in `Test` stdlib.
- `docs/`, an API reference built with
  [`Documenter.jl`](https://documenter.juliadocs.org/), analogous to how
  [`python/docs/`](../python/docs/) uses `quartodoc`.

## CI

`.github/workflows/book.yml` is already structured so that adding a Julia
docs build is additive: a new `build-julia-docs` job (rendering
`julia/docs/` to a `Documenter.jl` site) plus one more download/copy step in
the `deploy` job (publishing it under `reference/julia/`) — the existing
book and Python jobs wouldn't need to change.
