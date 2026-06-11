# Formal verification with Aeneas

This directory holds the [Aeneas](https://github.com/AeneasVerif/aeneas)-based
formal-verification setup for this repository. Aeneas verifies Rust by
translating it (via [Charon](https://github.com/AeneasVerif/charon)) into a pure
functional model in a proof assistant — here, **Lean 4** — over which we prove
properties.

```
Rust source ──(Charon)──▶ *.llbc ──(Aeneas)──▶ Lean 4 model ──(Lean+mathlib)──▶ proofs
```

## Layout

| Path | What |
|------|------|
| `aeneas-setup-log.txt` | **Reproducible, step-by-step toolchain install log** (read this first to set up a new machine). |
| `field/` | **Verification of the curve25519 field arithmetic** (`field.rs` + `FieldElement51`): complete-module Lean model, hand-written `subtle` external models, first proofs. See `field/README.md`. |
| `examples/smoke.rs` | Tiny standalone Rust file used to validate the pipeline. |
| `examples/smoke.llbc` | LLBC emitted by Charon (`--preset=aeneas`). |
| `examples/gen/Smoke.lean` | Lean model emitted by Aeneas. |
| `lean/Smoke.lean` | The generated model, in the Lean project. |
| `lean/SmokeProofs.lean` | Hand-written specs/proofs over the model (e.g. `add_spec`). |
| `lean/check.sh` | Turnkey: compiles the models + runs the proofs against the built Aeneas lib (seconds). |
| `lean/lakefile.lean` | Standard Lake project wiring (alternative to `check.sh`; pulls its own mathlib). |

## Toolchain location (installed outside the repo, in `$HOME`)

The Charon/Aeneas/opam toolchain lives in `$HOME` (outside the repo); the system
prerequisites (`opam`, `libgmp-dev`, `bubblewrap`) are installed via `apt`. See
`aeneas-setup-log.txt` for the full recipe — the MAIN route is this system
install; Appendix A is a no-root fallback. Before running any command:

```bash
source ~/aeneas-toolchain/env.sh   # sets PATH (opam/charon/aeneas) + opam env
```

- `charon`  → `~/aeneas-toolchain/aeneas/charon/bin/charon`
- `aeneas`  → `~/aeneas-toolchain/aeneas/bin/aeneas`
- Aeneas Lean library → `~/aeneas-toolchain/aeneas/backends/lean`

See `aeneas-setup-log.txt` for how these were built (and the non-obvious fixes).

## Regenerate the Lean model from Rust

```bash
source ~/aeneas-toolchain/env.sh
cd verification/examples
# 1. Rust -> LLBC  (the --preset=aeneas flag is REQUIRED by Aeneas)
charon rustc --preset=aeneas --dest-file smoke.llbc -- --crate-type lib --edition 2021 smoke.rs
# 2. LLBC -> Lean
aeneas -backend lean smoke.llbc -dest ./gen
```

## Build / check the Lean side

Fast path — reuses the already-built Aeneas library + mathlib (recommended):

```bash
cd verification/lean
./check.sh           # compiles Smoke.lean and verifies SmokeProofs.lean (~seconds)
```

Standard Lake path (materializes a second mathlib for this project):

```bash
source ~/aeneas-toolchain/env.sh
cd verification/lean
lake exe cache get   # download prebuilt mathlib oleans (avoids hours of compile)
lake build           # builds the generated models + proofs against the Aeneas lib
```

`SmokeProofs.lean` shows the verification workflow: state a spec as a Hoare-style
triple over the generated `Result`-monad function and discharge it with Aeneas'
`step`/`progress`/`grind` tactics. For example `add_spec` proves that the Rust
`add(x, y)` returns exactly `x + y` whenever it doesn't overflow a `u32`.

## Verifying the actual crypto crates (next phase)

The smoke test proves the pipeline. To target real code (e.g. field/scalar
arithmetic in `curve25519/solana-ed25519`), run Charon over the crate with
`charon cargo --preset=aeneas` and then Aeneas. Expect to iterate: Charon may
need `[package.metadata.charon]` options, and some constructs (inline asm,
SIMD intrinsics, certain `unsafe`) are not translatable and must be marked
opaque / given hand-written models. Track that work per-module here.
