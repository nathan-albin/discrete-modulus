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

- [`python/src/discrete_modulus/`](python/src/discrete_modulus/) — the Python
  library implementing the modulus algorithms (basic algorithm, family
  operators, NetworkX-based families, demo graphs), packaged as an
  installable module (`python/pyproject.toml`).
- [`book/`](book/) — the notebooks and pages that make up the companion book,
  currently built with Jupyter Book.
- [`requirements.txt`](requirements.txt) — pinned Python environment used to
  run the code and build the book. (Still repo-root for now; this will move
  into `python/pyproject.toml` in a later step — see PR #28.)

## Running the code

You'll need a Python environment with the packages listed in
[`requirements.txt`](requirements.txt), most notably:

- networkx
- numpy
- matplotlib
- cvxpy
- pycddlib
- jupyter

Install them into a virtual environment with:

```sh
pip install -r requirements.txt
```

Then install the library itself in editable mode:

```sh
pip install -e python/
```

Then start Jupyter in `book/` — the notebooks there are the source for the
book, and they import the library code via `import discrete_modulus`.

## Building the book

The book is currently built with [Jupyter Book](https://jupyterbook.org/).
With the Python environment above active, run from the `book/` directory:

```sh
jupyter-book build .
```

and publish the result to the `gh-pages` branch with:

```sh
ghp-import -n _build/html
```

(This will be replaced by a Quarto-based build in CI — see PR #28.)

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
