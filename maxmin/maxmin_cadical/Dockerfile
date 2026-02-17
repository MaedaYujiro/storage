# Multi-stage build for maxmin with runsolver

# === Builder stage ===
FROM rust:1.83-bookworm AS builder

# C++ build tools (required for cadical-sys, bddminisat-sys, and runsolver)
RUN apt-get update && apt-get install -y \
    cmake \
    clang \
    git \
    libnuma-dev \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /build

# Build runsolver
RUN git clone https://github.com/utpalbora/runsolver.git && \
    cd runsolver/src && \
    make

# Copy maxmin (including cp4rust)
COPY . /build/maxmin

# Build maxmin
WORKDIR /build/maxmin
RUN sed -i 's|edition = "2024"|edition = "2021"|' cp4rust/Cargo.toml && \
    cargo build --release

# === Runtime stage ===
FROM debian:bookworm-slim

# Install runtime dependencies for runsolver
RUN apt-get update && apt-get install -y \
    numactl \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /build/maxmin/target/release/maxmin /usr/local/bin/
COPY --from=builder /build/runsolver/src/runsolver /usr/local/bin/

# Default entrypoint: run maxmin via runsolver
# Usage: docker run -v /path/to/benchmark:/data maxmin [runsolver options] maxmin <solver> /data/graph.col
ENTRYPOINT ["runsolver"]
