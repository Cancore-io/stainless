#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

echo "=== 1/2: Checking committed vectors against the Python oracle ==="
python3 "$SCRIPT_DIR/scripts/oracle_gen.py" --check

echo "=== 2/2: Cross-validating the vectors on the JVM (sbt) ==="
cd "$REPO_ROOT"
sbt -batch "stainless-crypto-oracle / test"
