#!/usr/bin/env bash
# Regenerate the Lean model in gen/ from the Rust sources.
#
#   Rust (field.rs + backend/serial/u64/field.rs) --charon--> CurveField.llbc
#   CurveField.llbc --aeneas--> gen/CurveField/{Types,Funs,*_Template}.lean
#
# The hand-written gen/CurveField/{TypesExternal,FunsExternal}.lean are NOT
# touched by regeneration (Aeneas only rewrites the *_Template variants).
# After regenerating, diff the templates against the hand-written files to see
# whether new external items appeared:
#   diff gen/CurveField/FunsExternal_Template.lean gen/CurveField/FunsExternal.lean
#
# Usage:  ./extract.sh
set -euo pipefail

source ~/aeneas-toolchain/env.sh
HERE="$(cd "$(dirname "$0")" && pwd)"
CRATE="$HERE/../../curve25519/solana-ed25519"

echo "[1/2] charon: Rust -> LLBC (scoped to the field module tree)"
# --start-from     : translation roots = the two field modules (full closure pulled in)
# --opaque         : internal_invert_batch is dead code under these features and
#                    uses iterator rev/zip that Aeneas has no model for
# --no-default-features : field code needs none of alloc/zeroize/digest/
#                    precomputed-tables/rand_core; each only adds risk surface
# --preset=aeneas  : REQUIRED — Aeneas rejects LLBC produced without it
cd "$CRATE"
charon cargo --preset=aeneas \
  --start-from crate::field \
  --start-from crate::backend::serial::u64::field \
  --opaque 'crate::field::_::internal_invert_batch' \
  --dest-file "$HERE/CurveField.llbc" \
  -- --no-default-features

echo "[2/2] aeneas: LLBC -> Lean (split files, CurveField.* modules)"
cd "$HERE"
aeneas -backend lean -split-files -subdir CurveField -dest gen CurveField.llbc

echo "Done. Now run ./check.sh to type-check the regenerated model."
