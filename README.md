# discrete-modulus

Code and documentation for computing the **discrete modulus**
of families of objects on graphs. It serves as a reference implementation of the
theory, and includes a [companion
book](https://nathan-albin.com/discrete-modulus/) that introduces the theory and
walks through the code.

Currently the code includes a  Python library (`discrete_modulus`, located in
[`python/`](python/)) and a specialized C++ library ([`cpp/`](cpp/))
implementing an exact-arithmetic algorithm for computing spanning tree modulus.
[`julia/`](julia/) is a placeholder for a future Julia code. Each is an
**independent** implementation of the same underlying theory, they aren't intended to interoperate (yet).
[`lean/`](lean/) is a Lean 4 project, still early-stage, that will independently
verify certificates of optimality produced from the C++ solver's output, built
on top of [`lean-modulus`](https://github.com/nathan-albin/lean-modulus).

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
- [`lean/`](lean/) — a Lean 4 project (`DiscreteModulusCert`, managed with
  [Lake](https://github.com/leanprover/lake)) that kernel-checks
  certificates of spanning-tree-modulus optimality without trusting the C++
  solver's arithmetic. Depends on
  [`lean-modulus`](https://github.com/nathan-albin/lean-modulus) (pinned to a
  specific commit) for its graph/matroid infrastructure. See
  [`docs/certification/`](docs/certification/) for how this fits together
  with the C++ solver and the Python certificate builder.
- [`docs/certification/`](docs/certification/) — what a certificate is, how
  the solver/builder/verifier pipeline produces and checks one, and exactly
  what is (and isn't) trusted, with a worked example.
- [`.github/workflows/`](.github/workflows/) — CI: linting, tests (Python,
  C++, and Lean), and the book/docs build+deploy (see [CI](#ci) below).
- [`.devcontainer/`](.devcontainer/) — a devcontainer with Python, `uv`,
  the Quarto CLI, and the C++ toolchain (CMake, Boost, Doxygen)
  preinstalled (see [Development environment](#development-environment)
  below).

## Running the code

The package is managed with [`uv`](https://docs.astral.sh/uv/):

```sh
cd python
uv sync
```

This creates a `.venv` with the library and its runtime dependencies
(numpy, scipy, cvxpy, networkx). There are three more dependency groups for
other tasks, addable individually or together:

```sh
cd python
uv sync --group dev --group book --group docs
```

or `uv sync --all-groups` for everything at once.

- `dev` — `ruff`, `mypy`, `pytest`, for linting, type-checking, and testing:

  ```sh
  cd python
  uv sync --group dev
  uv run ruff check src/ tests/
  uv run mypy src/ tests/
  uv run pytest --cov --cov-report=term-missing
  ```

- `book` — Jupyter, matplotlib, `pycddlib`, needed to execute the book's
  code cells. `pycddlib` builds a C extension against `cddlib`'s headers
  (Ubuntu/Debian: `apt install libcdd-dev`) — already present in the
  devcontainer image. See "Building the book" below.
- `docs` — `mkdocs` + `mkdocstrings`, needed to build the Python API
  reference. See "Building the Python API reference" below.

The `.qmd` pages in `book/` import the library the same way, via
`import discrete_modulus`, in executable code cells.

## Building the book

The book is built with [Quarto](https://quarto.org/) — install the Quarto
CLI separately (it's not a Python package): see the
[get-started guide](https://quarto.org/docs/get-started/).

Quarto's Python code cells run via Jupyter, against the `uv`-managed
environment. `book/_environment` already points Quarto at it
(`QUARTO_PYTHON=../python/.venv/bin/python`):

```sh
cd python
uv sync --group book
cd ../book
quarto render
```

or, for live-reloading while editing:

```sh
cd python
uv sync --group book
cd ../book
quarto preview
```

## Building the Python API reference

```sh
cd python
uv sync --group docs
cd docs
uv run mkdocs build
```

or, for live-reloading while editing:

```sh
cd python
uv sync --group docs
cd docs
uv run mkdocs serve
```

`mkdocstrings` renders the reference pages directly from docstrings at
build time, driven by the `::: module.path` directives in
`python/docs/pages/reference/*.md`.

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

> [!WARNING]
> `-DCMAKE_BUILD_TYPE=Release` is critical. This is a CPU-bound algorithm, and
an unoptimized build is dramatically slower.

See [`cpp/README.md`](cpp/README.md) for more, including running the
`spt_mod` CLI.

## Building the Lean verifier

Kept out of the main devcontainer: Mathlib's binary cache alone is several
GB, only needed by contributors actually working on `lean/`. Run its setup
script once, which installs [`elan`](https://github.com/leanprover/elan) if
needed, then fetches dependencies and Mathlib's cache before building:

```sh
lean/setup.sh
```

Subsequent builds:

```sh
cd lean
lake build
```

## Building the C++ API reference

Requires [Doxygen](https://www.doxygen.nl/) (and, optionally,
[Graphviz](https://graphviz.org/) for diagrams):

```sh
cd cpp/docs
doxygen Doxyfile
```

generates `cpp/docs/_site/html/`.

## Development environment

The included devcontainer (`.devcontainer/`) has Python, `uv`, the Quarto
CLI, `libcdd-dev`, and the C++ toolchain (CMake, Boost, Doxygen, Graphviz)
preinstalled, and runs `uv sync --all-groups` on create — opening the repo
in it (VS Code's Dev Containers extension, or a Codespace) is enough to
lint, test, and build the book, the Python API docs, and the C++ library
immediately. The Lean toolchain is deliberately left out (see "Building the
Lean verifier" above) — run `lean/setup.sh` once if you need it.

## CI

- `lint.yml` — `ruff check`, `ruff format --check`, `mypy`, on changes
  under `python/`.
- `test.yml` — `pytest` across a Python version matrix, on changes under
  `python/`.
- `cpp-test.yml` — configures, builds, and runs the Catch2 test suite for
  `cpp/`, on changes under `cpp/`.
- `lean-test.yml` — installs `elan`, fetches Mathlib's cache, and runs
  `lake build` for `lean/`, on changes under `lean/`.
- `book.yml` — builds the book, the Python API reference, and the C++ API
  reference as independent jobs, then assembles them into one site (book
  at the root, API references under `reference/python/` and
  `reference/cpp/`) and publishes it to the `gh-pages` branch, on push to
  `main`. Structured so that adding a Julia docs build later only means
  adding one more build job and one more assembly step.

## License

BSD 3-Clause. See [`LICENSE`](LICENSE) for details.

Nathan Albin and Pietro Poggi-Corradini
