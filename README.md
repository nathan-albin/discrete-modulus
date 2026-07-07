# discrete-modulus

Reference implementations of algorithms for **discrete modulus**, a
combinatorial/optimization-based generalization of classical modulus of curve
families. Currently this means a Python library (`discrete_modulus`) and a
narrower C++ library (`cpp/`, exact spanning tree modulus only);
[`julia/`](julia/) is a placeholder for a future Julia reference
implementation. Each is an **independent** implementation of the same
underlying theory, not bindings or wrappers around the others — the
languages aren't meant to interoperate.

A companion book, built with Quarto from the pages in [`book/`](book/),
introduces the theory and walks through the code, with the Python API
reference (generated from docstrings via `mkdocstrings`) linked from it. Read
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
  - `python/docs/` — a standalone `mkdocs` site that generates the Python
    API reference from docstrings via `mkdocstrings`.
- [`book/`](book/) — the `.qmd` pages that make up the companion book, built
  with [Quarto](https://quarto.org/).
- [`cpp/`](cpp/) — the `discrete_modulus` C++ library (header-only,
  `cpp/include/discrete_modulus/`: exact spanning tree modulus via
  Cunningham's algorithm), built with CMake and Boost.Graph. Narrower in
  scope than `python/` so far — see [`cpp/README.md`](cpp/README.md).
  - `cpp/test/` — the Catch2 test suite.
  - `cpp/docs/` — Doxygen config for the API reference.
- [`julia/`](julia/) — not implemented yet; see its `README.md` for
  intended scope.
- [`.github/workflows/`](.github/workflows/) — CI: linting, tests (Python
  and C++), and the book/docs build+deploy (see [CI](#ci) below).
- [`.devcontainer/`](.devcontainer/) — a devcontainer with Python, `uv`,
  the Quarto CLI, and the C++ toolchain (CMake, Boost, Doxygen)
  preinstalled (see [Development environment](#development-environment)
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
- `docs` — `mkdocs` + `mkdocstrings`, needed to build the Python API
  reference.

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
uv run mkdocs build
```

or, for live-reloading while editing:

```sh
uv run mkdocs serve
```

`mkdocstrings` renders the reference pages directly from docstrings at
build time, driven by the `::: module.path` directives in
`python/docs/reference/*.md`.

## Building the C++ library

The `cpp/` library is built with [CMake](https://cmake.org/) (>= 3.20) and
requires [Boost](https://www.boost.org/) (>= 1.74, the `graph` component).
On Ubuntu/Debian: `apt install cmake libboost-graph-dev` (already present
in the devcontainer image).

```sh
cmake -S cpp -B cpp/build -DCMAKE_BUILD_TYPE=Release
cmake --build cpp/build
ctest --test-dir cpp/build --output-on-failure
```

(`-DCMAKE_BUILD_TYPE=Release` matters more than usual here — this is a
CPU-bound algorithm, and an unoptimized build is dramatically slower.)

See [`cpp/README.md`](cpp/README.md) for more, including running the
`spt_mod` CLI and building its Doxygen API reference.

## Development environment

The included devcontainer (`.devcontainer/`) has Python, `uv`, the Quarto
CLI, `libcdd-dev`, and the C++ toolchain (CMake, Boost, Doxygen, Graphviz)
preinstalled, and runs `uv sync --all-groups` on create — opening the repo
in it (VS Code's Dev Containers extension, or a Codespace) is enough to
lint, test, and build the book, the Python API docs, and the C++ library
immediately.

## CI

- `lint.yml` — `ruff check`, `ruff format --check`, `mypy`, on changes
  under `python/`.
- `test.yml` — `pytest` across a Python version matrix, on changes under
  `python/`.
- `cpp-test.yml` — configures, builds, and runs the Catch2 test suite for
  `cpp/`, on changes under `cpp/`.
- `book.yml` — builds the book, the Python API reference, and the C++ API
  reference as independent jobs, then assembles them into one site (book
  at the root, API references under `reference/python/` and
  `reference/cpp/`) and publishes it to the `gh-pages` branch, on push to
  `main`. Structured so that adding a Julia docs build later only means
  adding one more build job and one more assembly step.

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
