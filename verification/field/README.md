# Verifying `solana-ed25519` field arithmetic (mod p = 2²⁵⁵ − 19)

Aeneas-based verification workspace for the curve25519 field arithmetic: the
`FieldElement` API in [`src/field.rs`](../../curve25519/solana-ed25519/src/field.rs)
and its implementation `FieldElement51` in
[`src/backend/serial/u64/field.rs`](../../curve25519/solana-ed25519/src/backend/serial/u64/field.rs),
transpiled **as complete modules** (no function cherry-picking) to Lean 4.

```
field.rs + backend/serial/u64/field.rs ──charon──▶ CurveField.llbc ──aeneas──▶ gen/CurveField/*.lean
```

Everything in the closure is translated **transparently** (full bodies, zero
`sorry`), including `invert`, `pow22501`, `pow2k`, `square`, `from_bytes`,
`to_bytes`, `reduce` and the decompression-critical `sqrt_ratio_i`.

## Layout

| Path | What |
|------|------|
| `extract.sh` | Regenerates the model: Charon (Rust → LLBC) + Aeneas (LLBC → Lean). Idempotent; does not touch the hand-written files below. |
| `gen/CurveField/Types.lean`, `Funs.lean` | **Generated — do not edit.** The field model (~40 defs). |
| `gen/CurveField/*_Template.lean` | **Generated — do not edit.** Axiom skeletons for external items; diff against the hand-written versions after regenerating to spot new externals. |
| `gen/CurveField/TypesExternal.lean`, `FunsExternal.lean` | **Hand-written models** for external items (mostly `subtle`). See modeling policy below. |
| `Proofs/` | Hand-written proofs over the model (`Basic.lean`: external-model spec lemmas + first sanity facts). |
| `check.sh` | Type-checks gen/ + Proofs/ against the built Aeneas Lean library (reuses its mathlib — runs in seconds). |
| `CurveField.llbc` | Charon output (gitignored; regenerate via `extract.sh`). |

## Usage

```bash
source ~/aeneas-toolchain/env.sh   # toolchain per ../aeneas-setup-log.txt
./extract.sh                        # Rust -> LLBC -> Lean   (after changing Rust code)
./check.sh                          # type-check model + proofs
```

## Extraction decisions (why it looks like this)

* **Scope = the two field modules via `--start-from`.** A literal whole-crate
  run is blocked upstream: Aeneas crashes (internal `Not_found`) on other parts
  of the crate and on the 6000-line precomputed basepoint table; AVX2/SIMD and
  sha2 internals are untranslatable anyway. The field module tree + its closure
  is extracted complete.
* **`--no-default-features`.** The field code needs none of
  alloc/zeroize/digest/precomputed-tables/rand_core; each would only add
  untranslatable surface (e.g. the digest-gated `hash_to_field`/
  `expand_msg_xmd` iterator machinery).
* **`internal_invert_batch` is opaque** (axiom): dead code under these features
  (its only caller is alloc-gated) and its `rev/zip` iterator loops have no
  Aeneas model.
* **One source patch** in `src/field.rs::sqrt_ratio_i`:
  `r.conditional_negate(c)` was rewritten to
  `let r_neg = -&r; r.conditional_assign(&r_neg, c)` — semantically identical
  and still constant-time, but it avoids `subtle`'s `ConditionallyNegatable`
  blanket impl whose `for<'a> &'a T: Neg` bound crashes Aeneas
  ("Region ids should not be visited directly"). This keeps `sqrt_ratio_i`
  transparent instead of axiomatized. Full crate test suite: 153/153 pass.

## External-model policy (`gen/CurveField/*External.lean`)

The trusted base beyond Aeneas itself is exactly these models. Policy:

* **Faithful bit-level models** where the Rust body is real computation:
  `Choice::bitor` is bitwise or; `u8::ct_eq` decides equality (the spec the
  xor/shift trick implements); `u64::conditional_*` collapse the mask trick to
  if-then-else, exact on the documented `Choice` ∈ {0,1} invariant.
* **Identity models** where the Rust body is an optimization barrier:
  `Choice::from(u8)` / `black_box` volatile reads are semantically `id`;
  `subtle.Choice := U8` (reducible).
* **Trait-default bodies modeled by their actual defaults**
  (`conditional_assign` = `conditional_select`, etc.).
* **Slice `ct_eq`** is modeled as logical slice equality — exact for the only
  reachable instantiation (`T = u8`); caveat documented inline.
* **Remaining axioms** (4): `Debug::fmt`, raw-pointer `get_unchecked{,_mut}`,
  and the deliberately-opaque `internal_invert_batch` — none carry semantics
  field proofs rely on.

## Proof roadmap (next phase)

1. Limb-bound invariant `bounded fe k := ∀ i, (fe.val.get i).val < 2^(51+k)`
   and closure lemmas for `add`/`sub`/`negate`/`reduce` (panic-freedom of the
   carry chains = the `Result` never being `fail`).
2. Denotation `⟦fe⟧ : ZMod (2^255 - 19) := Σ limbᵢ · 2^(51·i)` and
   correctness of `mul`/`square`/`pow2k` against it (the u128 carry chain).
3. `from_bytes`/`to_bytes` round-trip and canonicity of `to_bytes`.
4. `invert` correct (via `pow22501` chain = x^(p−2)), `sqrt_ratio_i` spec.

`Proofs/Basic.lean` pins the external-model semantics as simp lemmas and
proves first sanity facts (`ZERO`, `default`, `from_limbs`) — use it as the
pattern; the Aeneas `step`/`progress`/`grind` tactics (see
`verification/lean/SmokeProofs.lean`) are the workhorses for the items above.
