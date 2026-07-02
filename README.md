# discrete-modulus

Reference implementations of algorithms for **discrete modulus**, a
combinatorial/optimization-based generalization of classical modulus of curve
families. Currently this means a Python library (`discrete_modulus`);
[`julia/`](julia/) and [`cpp/`](cpp/) are placeholders for future Julia and
C++ reference implementations. Those would be **independent**
implementations of the same underlying theory, not bindings or wrappers
around the Python code — the languages aren't meant to interoperate.

A companion book, built with Quarto from the pages in [`book/`](book/),
introduces the theory and walks through the code, with the Python API
reference (generated from docstrings via `quartodoc`) linked from it. Read
it here: **https://nathan-albin.com/discrete-modulus/**

> [!NOTE]
> This repository recently went through a restructuring (new name,
> code-first layout, modernized packaging, Quarto book, CI, devcontainer).
> That work is tracked in [PR #28](https://github.com/nathan-albin/discrete-modulus/pull/28).

## Repository layout

- [`python/`](python/) — the `discrete_modulus` Python package
  (`python/src/discrete_modulus/`: basic algorithm, family operators,
  NetworkX-based families, demo graphs), managed with
  [`uv`](https://docs.astral.sh/uv/) (`python/pyproject.toml` +
  `python/uv.lock`). Requires Python >= 3.11.
  - `python/tests/` — the `pytest` suite.
  - `python/docs/` — a standalone Quarto website that generates the Python
    API reference from docstrings via `quartodoc`.
- [`book/`](book/) — the `.qmd` pages that make up the companion book, built
  with [Quarto](https://quarto.org/).
- [`julia/`](julia/), [`cpp/`](cpp/) — not implemented yet; see their
  `README.md`s for intended scope.
- [`.github/workflows/`](.github/workflows/) — CI: linting, tests, and the
  book/docs build+deploy (see [CI](#ci) below).
- [`.devcontainer/`](.devcontainer/) — a devcontainer with Python, `uv`, and
  the Quarto CLI preinstalled (see [Development environment](#development-environment)
  below).

## Running the code

The package is managed with [`uv`](https://docs.astral.sh/uv/). From the
`python/` directory:

```sh
uv sync
```

This creates a `.venv` with the library and its runtime dependencies
(numpy, scipy, cvxpy, networkx). There are three more dependency groups for
other tasks, addable individually or together (`uv sync --group dev --group book --group docs`,
or `uv sync --all-groups` for everything at once):

- `dev` — `ruff`, `mypy`, `pytest`, for linting, type-checking, and testing:

  ```sh
  uv sync --group dev
  uv run ruff check src/ tests/
  uv run mypy src/ tests/
  uv run pytest --cov --cov-report=term-missing
  ```

- `book` — Jupyter, matplotlib, `pycddlib`, needed to execute the book's
  code cells. `pycddlib` builds a C extension against `cddlib`'s headers
  (Ubuntu/Debian: `apt install libcdd-dev`) — already present in the
  devcontainer image.
- `docs` — `quartodoc`, needed to build the Python API reference.

The `.qmd` pages in `book/` import the library the same way, via
`import discrete_modulus`, in executable code cells.

## Building the book

The book is built with [Quarto](https://quarto.org/) — install the Quarto
CLI separately (it's not a Python package): see the
[get-started guide](https://quarto.org/docs/get-started/).

Quarto's Python code cells run via Jupyter, against the `uv`-managed
environment (with the `book` group installed). `book/_environment` already
points Quarto at it (`QUARTO_PYTHON=../python/.venv/bin/python`), so no
manual setup is needed beyond `uv sync --group book` in `python/`. Then,
from the `book/` directory:

```sh
quarto render
```

or, for live-reloading while editing:

```sh
quarto preview
```

## Building the Python API reference

From `python/docs/`, with the `docs` group installed:

```sh
uv run python -m quartodoc build
quarto render
```

`quartodoc build` generates the reference pages from docstrings; since
`python/docs/` is a Quarto *website* project (not a book), every generated
page renders automatically — no manual chapter listing needed.

## Development environment

The included devcontainer (`.devcontainer/`) has Python, `uv`, the Quarto
CLI, and `libcdd-dev` preinstalled, and runs `uv sync --all-groups` on
create — opening the repo in it (VS Code's Dev Containers extension, or a
Codespace) is enough to lint, test, and build both the book and the API
docs immediately.

## CI

- `lint.yml` — `ruff check`, `ruff format --check`, `mypy`, on changes
  under `python/`.
- `test.yml` — `pytest` across a Python version matrix, on changes under
  `python/`.
- `book.yml` — builds the book and the Python API reference as independent
  jobs, then assembles them into one site (book at the root, API reference
  under `reference/python/`) and publishes it to the `gh-pages` branch, on
  push to `main`. Structured so that adding Julia/C++ docs later only means
  adding one more build job and one more assembly step.

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
