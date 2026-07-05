FROM mcr.microsoft.com/devcontainers/python:3.12-bookworm

# libcdd-dev: pycddlib (python/ 'book' dependency group) builds a C
# extension against cddlib's headers at install time.
# build-essential: belt-and-suspenders in case the base image ever drops it.
# cmake, libboost-graph-dev: cpp/'s CMake-built library (Boost.Graph).
# doxygen, graphviz: cpp/docs/'s Doxygen-generated API reference.
RUN apt-get update && apt-get install -y --no-install-recommends \
        libcdd-dev \
        build-essential \
        curl \
        ca-certificates \
        cmake \
        libboost-graph-dev \
        doxygen \
        graphviz \
    && rm -rf /var/lib/apt/lists/*

# Quarto CLI, pinned to the same version book.yml uses in CI.
ARG QUARTO_VERSION=1.9.38
ARG TARGETARCH
RUN curl -fsSL -o /tmp/quarto.deb \
        "https://github.com/quarto-dev/quarto-cli/releases/download/v${QUARTO_VERSION}/quarto-${QUARTO_VERSION}-linux-${TARGETARCH}.deb" \
    && dpkg -i /tmp/quarto.deb \
    && rm /tmp/quarto.deb

# uv, installed to a location on PATH for every user (not just root).
RUN curl -LsSf https://astral.sh/uv/install.sh | env UV_INSTALL_DIR=/usr/local/bin sh
