-- Hand-written models for external types (derived from TypesExternal_Template.lean).
-- [curve25519]: external types.
/- ──────────────────────────────────────────────────────────────────────────────────────────
   gen/CurveField/TypesExternal.lean — HAND-WRITTEN model of the external types

   When Charon+Aeneas transpile the Rust field modules (src/field.rs and
   src/backend/serial/u64/field.rs) to Lean, types defined OUTSIDE the extraction scope
   ("external" types) are not translated: the generator only emits an axiom skeleton,
   TypesExternal_Template.lean (`axiom subtle.Choice : Type` — "some type exists"). This
   file replaces that skeleton with a concrete, reviewable DEFINITION. Giving a model
   instead of keeping the axiom is strictly better for trust: nothing is postulated, and
   downstream proofs can actually compute with the type.

   Exactly one external type occurs in the closure of the field code: subtle::Choice, the
   constant-time boolean of the `subtle` crate.

   ROLE IN REACHING THE MAIN THEOREM
   Imported by Types.lean (and hence by Funs.lean / FunsExternal.lean / all of Proofs/).
   `Choice` appears in the signatures of `ct_eq`, `conditional_select/assign/swap` and
   `sqrt_ratio_i`; the totality-and-correctness statements of the main theorem
   (CurveFieldProofs.fieldImplementation, Proofs/FieldMain.lean) quantify over values of
   this type, so its model must be concrete. The companion function models live in
   FunsExternal.lean; Proofs/Basic.lean pins their semantics as `rfl` spec lemmas — only
   possible because `Choice` is a definition, not an axiom.

   This file is hand-written: ./extract.sh does NOT overwrite it (it only refreshes the
   *_Template.lean skeletons, which must stay byte-identical to the generator output —
   diff them after regenerating to spot newly appeared externals).
   ────────────────────────────────────────────────────────────────────────────────────────── -/
import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/-- [subtle::Choice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 120:0-120:17
    Name pattern: [subtle::Choice]

    MODEL: `Choice` is a transparent `u8` newtype carrying the (informal)
    invariant that its value is 0 or 1. The wrapper exists in Rust purely as an
    optimization barrier (`black_box` volatile read), which is semantically the
    identity, so we model the type as `U8` directly.

    subtle crate: `pub struct Choice(u8)` — a constant-time bool. Crypto code uses it
    instead of `bool` so the compiler cannot turn selections into data-dependent branches
    (a timing side channel). Verification cares about VALUES, not timing, so the wrapper
    contributes nothing semantically.

    ASCII semantics:  Choice = u8,  intended invariant c in {0,1},
                      "c as bool" = (c != 0),  1 = true, 0 = false.
    LaTeX: $\mathrm{Choice}\cong\{0,1\}\subset \mathbb{Z}/2^{8}$, truth value $c\neq 0$.

    WHY MODELING (vs translating) IS SOUND: the only way Rust code builds a `Choice` is
    `Choice::from(u8)`, whose body is `Choice(black_box(input))`; `black_box` is a volatile
    read — an optimization fence with identity value-semantics. So type-wise `Choice` IS a
    u8. The {0,1} invariant is not baked into the type; instead, every producer modeled in
    FunsExternal.lean (`ct_eq` returns the literal 0 or 1, `bitor` preserves {0,1}) only
    yields 0 or 1, and every consumer (`conditional_select` etc.) is modeled by comparing
    against 0 — exactly matching the Rust mask trick on that invariant.

    `@[reducible]` makes the equation `Choice = U8` transparent, so proofs may treat a
    `Choice` directly as a machine byte (e.g. `c.val : Nat`). -/
@[reducible, rust_type "subtle::Choice"]
def subtle.Choice : Type := Std.U8
