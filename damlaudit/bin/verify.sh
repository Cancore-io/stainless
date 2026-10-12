#!/usr/bin/env bash
# Run Stainless with the CI-parity config used by phd-auditor (smt-z3, 120 s, batched).
# Usage: verify.sh [--algebra] <files or dirs>... [-- extra stainless options]
#   --algebra   also pass the in-tree algebra library (frontends/algebra), which the
#               standalone stainless-library.jar does not ship.
# Env: STAINLESS          stainless launcher (default: stainless on PATH)
#      DAMLAUDIT_LOCK     if set, serialize the run with flock on this file
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
STAINLESS="${STAINLESS:-stainless}"

srcs=()
extra=()
while (($#)); do
  case "$1" in
    --algebra) mapfile -t alg < <(find "$ROOT/frontends/algebra/stainless" -name '*.scala' | sort); srcs+=("${alg[@]}") ;;
    --) shift; extra=("$@"); break ;;
    *) if [[ -d "$1" ]]; then mapfile -t found < <(find "$1" -name '*.scala' | sort); srcs+=("${found[@]}"); else srcs+=("$1"); fi ;;
  esac
  shift
done
((${#srcs[@]})) || { echo "usage: $0 [--algebra] <files or dirs>... [-- stainless options]" >&2; exit 2; }

cmd=("$STAINLESS" --solvers=smt-z3 --timeout=120 --batched=true "${extra[@]}" "${srcs[@]}")
if [[ -n "${DAMLAUDIT_LOCK:-}" ]]; then exec flock "$DAMLAUDIT_LOCK" "${cmd[@]}"; fi
exec "${cmd[@]}"
