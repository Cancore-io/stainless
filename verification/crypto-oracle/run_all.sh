#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== 1/3: Checking committed vectors against the Python Oracle ==="
python3 "$SCRIPT_DIR/scripts/oracle_gen.py" --check

echo "=== 2/3: Executing Python Oracle Test Suite ==="
python3 "$SCRIPT_DIR/tests/test_oracle.py"

echo "=== 3/3: Executing JVM / Scala Cross-Validation Suite ==="
scala "$SCRIPT_DIR/tests/CryptoOracleJvmTest.scala" -- "$SCRIPT_DIR/vectors"

echo "=========================================================="
echo ">>> SUCCESS: All Cryptographic Test Vectors Verified! <<<"
echo "=========================================================="
