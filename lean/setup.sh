#!/usr/bin/env bash
# One-time setup for working on the Lean verifier locally. Not run as part
# of the main devcontainer build: Mathlib's binary cache is several GB and
# only needed by contributors actually touching this directory.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")"

if ! command -v elan >/dev/null 2>&1; then
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
    # shellcheck disable=SC1090
    source "$HOME/.elan/env"
fi

lake update
lake exe cache get
lake build
