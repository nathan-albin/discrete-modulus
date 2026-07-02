# discrete-modulus

Reference implementations of algorithms for **discrete modulus**, a
combinatorial/optimization-based generalization of classical modulus of curve
families. Currently this means a Python library (`discrete_modulus`); the
plan is to add reference implementations in other languages (Julia, C++)
alongside it, since they aren't meant to interoperate — they're independent
implementations of the same underlying theory.

A companion book, built from the notebooks in this repository, introduces the
theory and walks through the code. Read it here:
**https://nathan-albin.com/discrete-modulus/**

> [!NOTE]
> This repository is in the middle of a restructuring (new name, code-first
> layout, modernized packaging, Quarto book, CI). Progress is tracked in
> [PR #28](https://github.com/nathan-albin/discrete-modulus/pull/28). The
> instructions below describe the *current* state of the repo, which will
> change as that work lands.

## Repository layout

- [`python/`](python/) — the `discrete_modulus` Python package
  (`python/src/discrete_modulus/`: basic algorithm, family operators,
  NetworkX-based families, demo graphs), managed with
  [`uv`](https://docs.astral.sh/uv/) (`python/pyproject.toml` +
  `python/uv.lock`). Requires Python >= 3.11.
- [`book/`](book/) — the notebooks and pages that make up the companion book,
  currently built with Jupyter Book.

## Running the code

The package is managed with [`uv`](https://docs.astral.sh/uv/). From the
`python/` directory:

```sh
uv sync
```

This creates a `.venv` with the library and its runtime dependencies
(numpy, scipy, cvxpy, networkx). To also get everything needed to run/build
the book (Jupyter, Jupyter Book, matplotlib, pycddlib), add the `book`
group:

```sh
uv sync --group book
```

`pycddlib` builds from source and needs the `cddlib` headers available on
the system (Ubuntu/Debian: `apt install libcdd-dev`) — this will be baked
into the devcontainer once that's set up (see PR #28).

There's also a `dev` group (`ruff`, `mypy`, `pytest`) for linting, type-checking, and testing:

```sh
uv sync --group dev
uv run ruff check src/
uv run mypy src/
uv run pytest --cov --cov-report=term-missing
```

Then start Jupyter from `book/` (e.g. `uv run --group book jupyter lab`) —
the notebooks there import the library via `import discrete_modulus`.

## Building the book

The book is currently built with [Jupyter Book](https://jupyterbook.org/).
With the `book` dependency group installed, run from the `book/` directory:

```sh
uv run --project ../python jupyter-book build .
```

and publish the result to the `gh-pages` branch with:

```sh
uv run --project ../python ghp-import -n _build/html
```

(This will be replaced by a Quarto-based build in CI — see PR #28.)

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
