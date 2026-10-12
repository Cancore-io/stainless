# damlaudit

`damlaudit` is the Cancore audit branch of Stainless. phd-auditor uses it as its verification
tool, both in CI and during manual audits of the Scala models behind our Daml contracts.

Home: <https://github.com/Cancore-io/stainless/tree/damlaudit>, a fork of
`epfl-lara/stainless`. Our upstream PRs are opened from branches of the same fork.

## Branch policy

* `damlaudit` = upstream `main` + every branch we open as a PR against `epfl-lara/stainless`.
* Changes land here **only by merge**: from upstream `main`, or from one of our upstream PR
  branches. Never commit code here that is not also in an upstream PR.
* The only exception is tooling under `damlaudit/` (scripts, pinned submodules), which is
  never proposed upstream.
* When an upstream PR is merged or reworked, re-merge upstream `main`; when one is closed,
  revert its merge here.

Merged PR branches:

| Branch | Upstream PR | Content |
| :--- | :--- | :--- |
| `feature/pr1-crypto-oracle` | not opened yet | Crypto reference oracle, test vectors, JVM suite (`verification/crypto-oracle`) |

## Pinned versions

| Component | Version | Source |
| :--- | :--- | :--- |
| Stainless | 0.10.2 (host release) | `stainless` on PATH, or `STAINLESS=...` |
| Z3 | 5.0.0 | shipped with the 0.10.2 release (`bin/package-standalone.sh`) |
| cvc5 | 1.3.4 | shipped with the 0.10.2 release |
| Princess | 2025-04-01 | inox submodule `37db9545` |
| bolts | `a02ca7fd` (2026-08-28) | submodule `damlaudit/bolts` |
| algebra | in tree | `frontends/algebra` (upstream PR #645, merged 2019) |

The standalone `stainless-library.jar` does not ship the algebra library, so `verify.sh --algebra`
passes its sources explicitly.

## Usage (phd-auditor)

```bash
git submodule update --init damlaudit/bolts
damlaudit/bin/verify.sh <models...>                  # smt-z3, --timeout=120, --batched=true
damlaudit/bin/verify.sh --algebra <models...>        # plus stainless.algebra._
damlaudit/bin/verify.sh <models...> -- --vc-cache=false   # extra Stainless options after --
DAMLAUDIT_LOCK=/tmp/claude-1000/heavy.lock damlaudit/bin/verify.sh ...   # serialize heavy runs on a shared host
```

The flags match CI on 0.10.2, where there is no native Z3: a lemma that only passes with
`nativez3` is not green. Reusable proofs (e.g. `algorithms/extended-gcd/MoreExtendedEuclidGCD.scala`)
are passed as extra sources from `damlaudit/bolts`.
