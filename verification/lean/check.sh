#!/usr/bin/env bash
# Type-check the Aeneas-generated models + hand-written proofs in this directory
# against the locally-built Aeneas Lean library. This reuses the Aeneas library's
# already-built mathlib (no second multi-GB clone), so it runs in seconds.
#
# Usage:  ./check.sh
# Prereq: toolchain set up per ../aeneas-setup-log.txt (Aeneas Lean lib built:
#         cd "$AENEAS_HOME/backends/lean" && lake exe cache get && lake build)
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"

cd "$AENEAS_LEAN"
# `lake env` exports LEAN_PATH for the Aeneas lib + mathlib + deps; we append
# this directory so `import Smoke` resolves to the freshly built Smoke.olean.
lake env bash -c "cd '$HERE' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD\" && \
  echo '· compiling generated model: Smoke.lean'   && lean -o Smoke.olean Smoke.lean && \
  echo '· checking proofs:           SmokeProofs.lean' && lean SmokeProofs.lean && \
  echo 'OK — models type-check and all proofs pass'"
