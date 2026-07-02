# discrete-modulus

Reference implementations of algorithms for **discrete modulus**, a
combinatorial/optimization-based generalization of classical modulus of curve
families. Currently this means a Python library (`discrete_modulus`); the
plan is to add reference implementations in other languages (Julia, C++)
alongside it, since they aren't meant to interoperate — they're independent
implementations of the same underlying theory.

A companion book, built with Quarto from the pages in [`book/`](book/),
introduces the theory and walks through the code. Read it here:
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
- [`book/`](book/) — the `.qmd` pages that make up the companion book, built
  with [Quarto](https://quarto.org/).

## Running the code

The package is managed with [`uv`](https://docs.astral.sh/uv/). From the
`python/` directory:

```sh
uv sync
```

This creates a `.venv` with the library and its runtime dependencies
(numpy, scipy, cvxpy, networkx). To also get everything needed to run/build
the book (Jupyter, matplotlib, pycddlib), add the `book` group:

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

The `.qmd` pages in `book/` import the library the same way, via
`import discrete_modulus`, in executable code cells.

## Building the book

The book is built with [Quarto](https://quarto.org/) — install the Quarto
CLI separately (it's not a Python package): see the
[get-started guide](https://quarto.org/docs/get-started/).

Quarto's Python code cells run via Jupyter, so point Quarto at the `uv`-managed
environment (with the `book` group installed) before rendering:

```sh
export QUARTO_PYTHON=/absolute/path/to/python/.venv/bin/python
```

Then, from the `book/` directory:

```sh
quarto render
```

or, for live-reloading while editing:

```sh
quarto preview
```

Publish the result to the `gh-pages` branch with:

```sh
quarto publish gh-pages
```

(CI will handle this automatically once set up — see PR #28.)

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
