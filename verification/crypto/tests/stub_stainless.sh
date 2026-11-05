#!/usr/bin/env bash
# Stand-in for Stainless in verify_sh_test.sh: replays STUB_GROUP1 (exit STUB_RC) for the group-1 run,
# a clean one-VC table for the PrattTraces chunks.
if [[ "$*" == *primeFactorListed* ]]; then cat "$STUB_GROUP1"; exit "$STUB_RC"; fi
echo '[ Info ] ║ total: 1 valid: 1 (0 from cache, 0 trivial) invalid: 0 unknown: 0 time: 0.10 ║'
