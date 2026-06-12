#!/usr/bin/env bash
# Type-check the Aeneas-generated field model + hand-written externals/proofs
# against the locally-built Aeneas Lean library. Reuses the Aeneas library's
# already-built mathlib (no second multi-GB clone), so it runs in seconds.
#
# Usage:  ./check.sh
# Prereq: toolchain per ../aeneas-setup-log.txt (Aeneas Lean lib built:
#         cd "$AENEAS_HOME/backends/lean" && lake exe cache get && lake build)
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
AENEAS_LEAN="$AENEAS_HOME/backends/lean"

# Compile order respects the import graph:
#   TypesExternal -> Types -> FunsExternal -> Funs -> Proofs/* (dependency order)
MODULES=(
  CurveField/TypesExternal
  CurveField/Types
  CurveField/FunsExternal
  CurveField/Funs
)

# Proofs in dependency order (Basic is standalone; FieldMain is the main result)
PROOFS=(
  Basic
  Denote
  P25519
  ReduceSpec
  SubNegSpec
  ConstSpecs
  AddSpec
  MulSpec
  SquareSpec
  Field
  InvertSpec
  FieldMain
  FeQ
)

cd "$AENEAS_LEAN"
# `lake env` exports LEAN_PATH for the Aeneas lib + mathlib + deps; we append
# gen/ (and the workspace root for Proofs) so `import CurveField.*` resolves.
lake env bash -c "
  set -euo pipefail
  cd '$HERE/gen' && export LEAN_PATH=\"\$LEAN_PATH:\$PWD:$HERE\"
  for m in ${MODULES[*]}; do
    echo \"· compiling \$m.lean\"
    lean -o \"\$m.olean\" \"\$m.lean\"
  done
  cd '$HERE'
  for m in ${PROOFS[*]}; do
    [ -f \"Proofs/\$m.lean\" ] || continue
    echo \"· checking  Proofs/\$m.lean\"
    lean -o \"Proofs/\$m.olean\" \"Proofs/\$m.lean\"
  done
  echo 'OK — field model type-checks and all proofs pass'
"
