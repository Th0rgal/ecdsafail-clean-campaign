#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"

cd "${ROOT_DIR}"

echo "=== [1/3] Building Lean 4 verifier (lean-verifier) ==="
lake build

echo "=== [2/3] Building & running Rust differential test suite generator ==="
(cd "${ROOT_DIR}/rust_diff_driver" && cargo build --release --offline --quiet)
SUITE_BIN="${ROOT_DIR}/.lake/build/diff_suite.bin"
"${ROOT_DIR}/rust_diff_driver/target/release/rust_diff_driver" gen-diff-suite "${SUITE_BIN}"

echo "=== [3/3] Running Lean 4 differential verifier against Rust reference traces ==="
"${ROOT_DIR}/.lake/build/bin/lean-verifier" diff-test "${SUITE_BIN}"
