#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "=== 1/3: Generating reference test vectors with Python Oracle ==="
python3 "$SCRIPT_DIR/scripts/oracle_gen.py"

echo "=== 2/3: Executing Python Oracle Test Suite ==="
python3 "$SCRIPT_DIR/tests/test_oracle.py"

echo "=== 3/3: Executing JVM / Scala Cross-Validation Suite ==="
scala "$SCRIPT_DIR/tests/CryptoOracleJvmTest.scala"

echo "=========================================================="
echo ">>> SUCCESS: All Cryptographic Test Vectors Verified! <<<"
echo "=========================================================="
