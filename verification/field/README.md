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
| `extract.sh` | Regenerates the model: Charon (Rust → LLBC) + Aeneas (LLBC → Lean). Idempotent; does not touch the hand-written files below. **Caveat:** regeneration emits the *bare* model — the explanatory doc comments in `Types.lean`/`Funs.lean` were added post-generation (the code tokens are untouched); recover them from git history after a regeneration. |
| `gen/CurveField/Types.lean`, `Funs.lean` | **Generated — do not edit code.** The field model (~40 defs), annotated post-generation with Rust-analog and math documentation. |
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

## Field theorem (Proofs/)

**The transpiled code is proven to implement the field 𝔽_p, p = 2²⁵⁵−19** —
without modifying anything in `gen/`. Main result:
`CurveFieldProofs.fieldImplementation : IsFieldImplementation`
([Proofs/FieldMain.lean](Proofs/FieldMain.lean)), axiom-clean
(`propext, Classical.choice, Quot.sound` only — no `sorry`, no `native_decide`).

| File | Result |
|------|--------|
| `Proofs/Denote.lean` | Denotation ⟪·⟫ : Fe → 𝔽_p (= mathlib `ZMod P`), limb-bound invariant `Bnd`. |
| `Proofs/P25519.lean` | `Nat.Prime (2^255 − 19)` — full Lucas/Pratt certificate chain, kernel-checked. |
| `Proofs/ReduceSpec.lean` | `reduce`: total, output < 2⁵², value preserved mod p (exact ℕ accounting). |
| `Proofs/AddSpec.lean` | `add` (the Rust `for`-loop): total under pairwise-sum < 2⁶⁴, limbwise exact. |
| `Proofs/SubNegSpec.lean` | `sub`/`negate` (16p trick): total under 2⁵⁴, ⟪·⟫ subtracts/negates. |
| `Proofs/MulSpec.lean` | `mul` (schoolbook, 19-folded, u128 carries): total under 2⁵⁴ (incl. the in-code `debug_assert`s), ⟪·⟫ multiplies. |
| `Proofs/SquareSpec.lean` | `pow2k` loop (induction) + `square`: ⟪·⟫ = x^(2^k). |
| `Proofs/ConstSpecs.lean` | `ZERO`/`ONE`/`MINUS_ONE`/`SQRT_M1` denote 0, 1, −1, √−1. |
| `Proofs/InvertSpec.lean` | `invert` = x^(p−2) via the pow22501 chain; equals x⁻¹ by Fermat. |
| `Proofs/Field.lean` | `Fact P.Prime` ⇒ `Field 𝔽_p`; `encode` ⇒ ⟪·⟫ surjective. |
| `Proofs/FieldMain.lean` | **`fieldImplementation`** + the field axioms at implementation level: `impl_add_comm/assoc`, `impl_zero_add`, `impl_add_neg`, `impl_mul_comm/assoc`, `impl_one_mul`, `impl_mul_inv_cancel`, `impl_left_distrib`, `impl_zero_ne_one`. |

Reading of the theorem: the representation is redundant (many limb vectors
denote one field element) and machine ops are partial, so "is a field" is
stated the standard way for crypto implementations: 𝔽_p is a field, ⟪·⟫ is
surjective, every transpiled op is **total on the documented invariant**
(no overflow/panic — this includes proving the Rust `debug_assert!` bounds)
and realizes the corresponding 𝔽_p operation through ⟪·⟫; all field axioms
then hold for the implementation up to denotation (the `impl_*` corollaries).

Trusted base beyond Lean+mathlib+Aeneas: the hand-written external models in
`gen/CurveField/*External.lean` (the `subtle` crate, documented per-item).
The unused axioms there (`Debug::fmt`, raw-ptr getters, the opaque batch
helper) are NOT in the dependency cone of the field theorems.

No security findings: every overflow side condition and both
`debug_assert!`s discharged under the dalek 2⁵⁴ limb discipline. One caveat
documented: `pow2k(_, 0)` would wrap `k−1` in release Rust (callers all pass
constants ≥ 1; the model enforces k ≥ 1 via the surviving `massert`).

## Edwards point arithmetic (Tier 1): the addition-law theorem (Proofs/Ed*.lean)

**The transpiled point operations are proven to implement the complete twisted
Edwards addition law** — `CurveFieldProofs.edwardsImplementation :
IsEdwardsImplementation` ([Proofs/EdMain.lean](Proofs/EdMain.lean)), axiom-clean.
For valid on-curve inputs, the transpiled `EdwardsPoint` add / sub / double /
neg / identity are total (no panic — every limb bound and `debug_assert`
discharged) and denote, via (x,y) = (X/Z, Y/Z), exactly to

    edAdd (x1,y1) (x2,y2) = ( (x1*y2 + x2*y1) / (1 + d*x1*x2*y1*y2),
                              (y1*y2 + x1*x2) / (1 - d*x1*x2*y1*y2) )

with d = -121665/121666. The extraction was widened to include
`backend::serial::curve_models` + `edwards` (same `CurveField` module; the 14
field/FeQ proof files compile unchanged; scalar-mul/AVX2/decompress remain
opaque — out of scope).

| File | Result |
|------|--------|
| `Proofs/EdCurve.lean` | The math layer: `edD`, `OnCurve`, `edAdd`, **`edD_not_square`** (kernel Euler criterion), **`completeness`** (Bernstein–Lange: denominators never vanish), `edAdd_closure`, id/neg/comm laws. |
| `Proofs/Square2Spec.lean` | `square2` = 2a² (the op point doubling needs). |
| `Proofs/EdDenote.lean` | Validity predicates for all 5 representations (with the **explicit `Z ≠ 0`** the Rust leaves implicit), denotations, `EDWARDS_D`/`D2` kernel-checked constant specs, identity runners. |
| `Proofs/EdDouble · EdAddProjNiels · EdAddAffNiels · EdConvert.lean` | Coordinate-exact specs of every transpiled formula (HWCD mixed add/sub ×4, dbl-2008-bbjlp double, conversions, negs) with honest per-coordinate limb bounds. |
| `Proofs/EdMain.lean` | **`edwardsImplementation`**: top-level add/sub/double/neg/identity law theorems + `impl_add_comm_ed`, `impl_add_id_ed`, `impl_add_neg_ed`. |

Not claimed (Tier 2 / future): associativity of `edAdd` (would come from the
birational map to mathlib's Weierstrass group), scalar multiplication
(blocked on upstream Aeneas internal errors), decompress/compress, and the
AVX2 vector backend.
