#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <ops.bin> [shots]" >&2
  exit 1
fi

OPS_BIN="$1"
SHOTS="${2:-64}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
CAMPAIGN_DIR="/var/lib/sandboxed-node/3bcb57a6-0a96-404c-bb04-1b1e22180951/ecdsafail-clean-campaign"

cd "${ROOT_DIR}"

BATCH_BIN="${ROOT_DIR}/.lake/build/pregate_batch_${SHOTS}.bin"

echo "=== [Pre-Gate Step 1/2] Exporting ${SHOTS}-shot Fiat-Shamir test batch + XOF stream ==="
"${ROOT_DIR}/rust_diff_driver/target/release/rust_diff_driver" export-batch "${OPS_BIN}" "${BATCH_BIN}" "${SHOTS}"

echo "=== [Pre-Gate Step 2/2] Evaluating full circuit & checking certificate in Lean 4 ==="
"${ROOT_DIR}/.lake/build/bin/lean-verifier" pregate "${OPS_BIN}" "${BATCH_BIN}" "${CAMPAIGN_DIR}"
