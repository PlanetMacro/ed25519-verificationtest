-- Hand-written models for external functions (derived from FunsExternal_Template.lean).
-- [curve25519]: external functions.
--
-- Modeling policy (see ../../README.md):
--  * `subtle` items whose Rust bodies are real bit math are modeled FAITHFULLY
--    (bitwise or, mask-based select collapses to if-then-else only on the
--    documented {0,1} Choice invariant — noted per item).
--  * `subtle` items whose Rust bodies are optimization barriers
--    (`black_box`/volatile reads) are semantically the identity and modeled so.
--  * core RangeFull slice indexing (`s[..]`) is the identity on the slice.
--  * Remaining axioms (Debug fmt, raw-pointer get_unchecked*, the deliberately
--    opaque `internal_invert_batch`) carry no semantics field proofs rely on.
/- ──────────────────────────────────────────────────────────────────────────────────────────
   gen/CurveField/FunsExternal.lean — HAND-WRITTEN models of the external functions

   When Charon+Aeneas transpile the Rust field modules (src/field.rs and
   src/backend/serial/u64/field.rs), functions defined OUTSIDE the extraction scope —
   the `subtle` crate (constant-time utilities) and a few `core` slice/format items — are
   not translated. The generator emits only typed axiom skeletons
   (FunsExternal_Template.lean: "a function of this type exists", no behavior). This file
   replaces each skeleton with either
     (a) a concrete DEFINITION (a model) when the field proofs need its behavior, or
     (b) the original AXIOM, kept only when nothing in the proof cone depends on it.
   Together with TypesExternal.lean these models are the entire trusted base beyond
   Lean + mathlib + Aeneas itself: each `def` here is a claim "this is what the Rust body
   computes", justified item-by-item in the docstrings below.

   WHY MODELING (vs translating) IS SOUND — the three recurring arguments:
     * black_box = identity: `core::hint::black_box` / volatile reads are compiler
       optimization fences; their VALUE semantics is `id`. (Choice::from, Choice -> u8.)
     * ct_eq = equality: subtle's xor/wrapping-neg/shift bit trick returns 1 iff the two
       integers are equal, 0 otherwise, for ALL inputs — i.e. it decides `a = b`; we model
       the specification directly.
     * masks on {0,1}: `a ^ (mask & (a ^ b))` with mask = (0 - c) mod 2^64 equals `a` when
       c = 0 (mask = 0) and `b` when c = 1 (mask = all ones). Every Choice produced by the
       models here is literally 0 or 1, so `if c.val = 0 then a else b` is exact.

   ROLE IN REACHING THE MAIN THEOREM
   Imports Types.lean; the trait-implementation records in Funs.lean plug these functions
   in as method fields (e.g. `U8.Insts.SubtleConstantTimeEq`), so the transpiled bodies of
   `ct_eq`, `conditional_select/assign`, `sqrt_ratio_i`, ... call into the models below.
   Proofs/Basic.lean re-states each model as a `rfl` spec lemma; the totality/correctness
   theorems culminating in CurveFieldProofs.fieldImplementation (Proofs/FieldMain.lean)
   unfold through them. The unused axioms kept here (Debug fmt, raw-pointer getters,
   internal_invert_batch) are NOT in the dependency cone of the field theorem.

   This file is hand-written: ./extract.sh does NOT overwrite it; after regenerating, diff
   FunsExternal_Template.lean against this file to spot newly appeared externals.
   ────────────────────────────────────────────────────────────────────────────────────────── -/
import Aeneas
import CurveField.Types
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048
open curve25519

-- ──────────────────────────────────────────────────────────────────────────────────────────
-- core std items: Debug formatting (axiom, unused) and RangeFull (`s[..]`) slice indexing.
-- ──────────────────────────────────────────────────────────────────────────────────────────

/-- [core::fmt::{impl core::fmt::Debug for [T]}::fmt]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 3122:4-3122:50
    Name pattern: [core::fmt::{core::fmt::Debug<[@T]>}::fmt]
    Visibility: public

    AXIOM: only reachable from the `Debug` impl; no field proof depends on it.

    Rust std analog: the `Debug` formatter for slices `[T]` (what `{:?}` calls).
    Only caller in the model: the translated `impl Debug for FieldElement51`
    (curve25519/solana-ed25519/src/backend/serial/u64/field.rs:46-48), which the field
    theorem never invokes. An axiom of FUNCTION type merely asserts such a function exists
    (any formatter would do) — it postulates no equation, so it cannot make anything
    provable about field arithmetic. Kept as an axiom because Funs.lean's Debug instance
    record must reference something of this type. -/
@[rust_fun "core::fmt::{core::fmt::Debug<[@T]>}::fmt"]
axiom Slice.Insts.CoreFmtDebug.fmt
  {T : Type} (DebugInst : core.fmt.Debug T) :
  Slice T → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 660:4-660:51
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut]

    MODEL: `&mut s[..]` is the whole slice; the backward function is the
    identity update.

    Rust std analog: `<RangeFull as SliceIndex<[T]>>::index_mut` — mutable full-range
    indexing, `&mut s[..]`.
    ASCII:  index_mut(_, s) = ok (s, fun s' => s')
    The returned PAIR is Aeneas's functional encoding of a mutable borrow: first component
    = the value the borrow currently sees (here: all of `s`); second component = the
    "write-back" function applied when the borrow ends (here: the new slice replaces the
    old one unchanged — the identity update). Since `..` selects everything and is always
    in range, the operation cannot fail: it is total (`ok`).
    WHY NEEDED: completes the `SliceIndex RangeFull [T]` instance in Funs.lean (all six
    methods must be populated for the record to typecheck). -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index_mut"]
def
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result ((Slice T) × (Slice T → Slice T)) :=
  ok (s, fun s' => s')

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::index]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 655:4-655:39
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index]

    MODEL: `&s[..]` is the whole slice.

    Rust std analog: `<RangeFull as SliceIndex<[T]>>::index` — shared full-range indexing,
    `&s[..]`.
    ASCII:  index(_, s) = ok s   (total: full range is always in bounds).
    WHY NEEDED: this is the method the translated `Debug` impl of FieldElement51 actually
    calls (`&self.0[..]` in backend/serial/u64/field.rs:47); also completes the
    `SliceIndex RangeFull [T]` instance in Funs.lean. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::index"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Slice T) :=
  ok s

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 650:4-650:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut]

    AXIOM: raw-pointer API, never called by the extracted field code.

    Rust std analog: the `unsafe` unchecked variant of `index_mut` (no bounds check,
    operates on raw pointers). The extracted field code never reaches it; the axiom only
    asserts a function of this type exists, with no equations — it carries no semantics any
    proof could use. Kept because the `SliceIndex` instance record in Funs.lean has a slot
    for it. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked_mut"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut
  {T : Type} :
  core.ops.range.RangeFull → MutRawPtr (Slice T) → Result (MutRawPtr (Slice
    T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_unchecked]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 645:4-645:66
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked]

    AXIOM: raw-pointer API, never called by the extracted field code.

    Rust std analog: the `unsafe` unchecked variant of `index` (no bounds check, raw
    pointers). Same status as `get_unchecked_mut` above: an equation-free axiom filling a
    mandatory slot of the `SliceIndex` instance record in Funs.lean; not in the proof
    cone. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_unchecked"]
axiom
  core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked
  {T : Type} :
  core.ops.range.RangeFull → ConstRawPtr (Slice T) → Result (ConstRawPtr
    (Slice T))

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get_mut]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 640:4-640:57
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut]

    MODEL: always `some` (RangeFull never fails); backward function folds an
    updated `some` back into the slice and keeps the original on `none`.

    Rust std analog: `s.get_mut(..)` — the `Option`-returning checked variant of
    `index_mut`.
    ASCII:  get_mut(_, s) = ok (some s, fun o => o.getD s)
    Forward: full-range lookup always succeeds, so the result is `some s` (never `none`).
    Backward (the mutable-borrow write-back, cf. `index_mut` above): the caller hands back
    a possibly-updated `Option (Slice T)`; `o.getD s` ("get-or-default") extracts `s'`
    from `some s'` and falls back to the original `s` on `none`.
    WHY NEEDED: completes the `SliceIndex RangeFull [T]` instance record in Funs.lean. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get_mut"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  ok (some s, fun o => o.getD s)

/-- [core::slice::index::{impl core::slice::index::SliceIndex<[T], [T]> for core::ops::range::RangeFull}::get]:
    Source: '/rustc/library/core/src/slice/index.rs', lines 635:4-635:45
    Name pattern: [core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get]

    MODEL: always `some` (RangeFull never fails).

    Rust std analog: `s.get(..)` — the `Option`-returning checked variant of `index`.
    ASCII:  get(_, s) = ok (some s)   (full-range lookup is always in bounds).
    WHY NEEDED: completes the `SliceIndex RangeFull [T]` instance record in Funs.lean. -/
@[rust_fun
  "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFull, [@T], [@T]>}::get"]
def core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  Result (Option (Slice T)) :=
  ok (some s)

-- ──────────────────────────────────────────────────────────────────────────────────────────
-- `subtle` crate models: conversions, bit-or, constant-time equality, conditional select.
-- `Choice` is modeled as `U8` (TypesExternal.lean); invariant: its value is 0 or 1.
-- ──────────────────────────────────────────────────────────────────────────────────────────

/-- [subtle::{impl core::convert::From<subtle::Choice> for bool}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 153:4-153:35
    Name pattern: [subtle::{core::convert::From<bool, subtle::Choice>}::from]

    MODEL (faithful): Rust body is `source.0 != 0`.

    subtle crate: `impl From<Choice> for bool` — unwrap a constant-time bool into a real
    `bool` (the point where constant-time code is allowed to branch).
    ASCII:  from(c) = ok (c != 0)     i.e. ok true iff the byte is non-zero.
    Faithful for ALL u8 values, not just {0,1} — no invariant needed.
    WHY NEEDED: Rust `impl PartialEq for FieldElement51` is `self.ct_eq(other).into()`
    (src/field.rs:51-55); the translated `eq` in Funs.lean ends with this call, so the
    proofs that `==` decides denotational equality unfold through this model. -/
@[rust_fun "subtle::{core::convert::From<bool, subtle::Choice>}::from"]
def Bool.Insts.CoreConvertFromChoice.from (c : subtle.Choice) : Result Bool :=
  ok (c.val != 0)

/-- [subtle::{impl core::ops::bit::BitOr<subtle::Choice, subtle::Choice> for subtle::Choice}::bitor]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 177:4-177:41
    Name pattern: [subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor]

    MODEL (faithful): Rust body is `(self.0 | rhs.0).into()`, and the `.into()`
    (`Choice::from`) is an optimization barrier = identity. Bitwise or on u8.

    subtle crate: `impl BitOr for Choice` — boolean OR without branching.
    ASCII:  bitor(a, b) = ok (a | b)      (bitwise or on the underlying u8)
    On the {0,1} invariant this is exactly boolean disjunction (0|0=0, else 1), and it
    PRESERVES the invariant: a, b in {0,1} ==> a|b in {0,1}.
    WHY NEEDED: `sqrt_ratio_i` (src/field.rs) computes
    `flipped_sign_sqrt | flipped_sign_sqrt_i` and `correct_sign_sqrt | flipped_sign_sqrt`
    to combine its three `ct_eq` checks; the sqrt-spec proof unfolds these through this
    model. -/
@[rust_fun
  "subtle::{core::ops::bit::BitOr<subtle::Choice, subtle::Choice, subtle::Choice>}::bitor"]
def subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor
  (a b : subtle.Choice) : Result subtle.Choice :=
  ok (a ||| b)

/-- [subtle::{impl core::convert::From<u8> for subtle::Choice}::from]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 238:4-238:32
    Name pattern: [subtle::{core::convert::From<subtle::Choice, u8>}::from]

    MODEL (faithful): Rust body is `Choice(black_box(input))`; the volatile
    read in `black_box` is semantically the identity.

    subtle crate: `impl From<u8> for Choice` — the ONLY constructor of `Choice`.
    ASCII:  from(b) = ok b      (identity, since Choice = U8 in our model)
    `black_box` is a compiler fence that stops the optimizer from reasoning about the
    value; it returns its argument unchanged, so its value semantics is `id`. Callers are
    documented (and verified in the crate) to pass only 0 or 1, which is where the {0,1}
    Choice invariant originates.
    WHY NEEDED: every `ct_eq` in subtle ends in `.into()` = this function; the translated
    code in Funs.lean calls it whenever a Choice is built from a byte (e.g. `is_negative`,
    `is_zero` in src/field.rs). -/
@[rust_fun "subtle::{core::convert::From<subtle::Choice, u8>}::from"]
def subtle.Choice.Insts.CoreConvertFromU8.from
  (b : Std.U8) : Result subtle.Choice :=
  ok b

/-- [subtle::{impl subtle::ConstantTimeEq for [T]}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 313:4-313:41
    Name pattern: [subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq]

    MODEL: 1 iff the slices are equal (length + elementwise), else 0.
    CAVEAT: this equates `ConstantTimeEqInst.ct_eq` with logical equality on
    `T`. That is exact for the only instantiation reachable from the field
    code (`T = u8`, whose `ct_eq` is genuine equality); a hypothetical exotic
    `ConstantTimeEq` instance would not be modeled faithfully.

    subtle crate: `impl ConstantTimeEq for [T]` — the Rust body checks the lengths, then
    folds `&=` over the elementwise `ct_eq`s (an iterator loop, hence not translatable by
    Aeneas and modeled here instead).
    ASCII:  ct_eq(a, b) = ok (if a = b then 1 else 0)
    LaTeX:  $\mathrm{ct\_eq}(a,b)=\mathbf{1}[a=b]$ — the indicator of slice equality.
    `noncomputable` + `open Classical`: equality of `List T` for an ARBITRARY `T` is not
    decidable by an algorithm, so the `if` uses the classical (nonconstructive) decision;
    proofs only need the propositional characterization, never evaluation.
    WHY NEEDED: `FieldElement51::ct_eq` (src/field.rs:57-64) compares
    `self.to_bytes()` with `other.to_bytes()`; subtle's `[u8; 32]` instance forwards to
    this slice instance via `self[..].ct_eq(&rhs[..])`. Equality/zero-test correctness in
    the proofs reduces to this model plus `to_bytes` canonicity. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<[@T]>}::ct_eq"]
noncomputable def Slice.Insts.SubtleConstantTimeEq.ct_eq
  {T : Type} (ConstantTimeEqInst : subtle.ConstantTimeEq T)
  (a b : Slice T) : Result subtle.Choice :=
  open Classical in
  ok (if a.val = b.val then 1#u8 else 0#u8)

/-- [subtle::{impl subtle::ConstantTimeEq for u8}::ct_eq]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 348:12-348:51
    Name pattern: [subtle::{subtle::ConstantTimeEq<u8>}::ct_eq]

    MODEL: 1 iff equal, else 0 — the specification the Rust xor/shift bit
    trick implements for all inputs.

    subtle crate: `impl ConstantTimeEq for u8`.
    ASCII:  ct_eq(a, b) = ok (if a = b then 1 else 0)
    The Rust body is branch-free bit math: with x = a XOR b (zero iff a = b), the
    expression `x | x.wrapping_neg()` has its top bit set iff x != 0; shifting it down and
    xoring with 1 yields exactly 1 when a = b and 0 otherwise — for ALL 2^16 input pairs.
    We model that specification directly; note the result is literally 0 or 1, which
    establishes the {0,1} Choice invariant for all equality tests.
    WHY NEEDED: this is the element-level test under `FieldElement51::ct_eq` (byte-string
    comparison); Proofs/Basic.lean pins it as the `rfl` lemma `u8_ct_eq_spec`. -/
@[rust_fun "subtle::{subtle::ConstantTimeEq<u8>}::ct_eq"]
def U8.Insts.SubtleConstantTimeEq.ct_eq
  (a b : Std.U8) : Result subtle.Choice :=
  ok (if a = b then 1#u8 else 0#u8)

/-- [subtle::ConditionallySelectable::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 442:4-442:66
    Name pattern: [subtle::ConditionallySelectable::conditional_assign]

    MODEL (faithful): the trait's default body is
    `*self = Self::conditional_select(self, other, choice)`.

    subtle crate: `ConditionallySelectable::conditional_assign` DEFAULT method body (the
    one a Rust impl inherits when it does not override the method). Generic over the
    instance dictionary `ConditionallySelectableInst`, exactly like the Rust default is
    generic over `Self`.
    ASCII:  conditional_assign(self, other, c) = conditional_select(self, other, c)
    (the `&mut self` write-back is the functional return value, cf. Types.lean).
    WHY NEEDED: trait-method calls on types that use the default resolve here; faithful by
    construction — it IS the default body, delegating to whatever `conditional_select` the
    instance supplies. -/
@[rust_fun "subtle::ConditionallySelectable::conditional_assign"]
def subtle.ConditionallySelectable.conditional_assign.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) (self other : Self) (choice : subtle.Choice) : Result Self :=
  ConditionallySelectableInst.conditional_select self other choice

/-- [subtle::ConditionallySelectable::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 469:4-469:67
    Name pattern: [subtle::ConditionallySelectable::conditional_swap]

    MODEL (faithful): the trait's default body conditionally assigns each side
    the other's original value.

    subtle crate: `ConditionallySelectable::conditional_swap` DEFAULT method body.
    ASCII:  a1 = conditional_assign(a, b, c);  b1 = conditional_assign(b, a, c);
            conditional_swap(a, b, c) = ok (a1, b1)
    On the {0,1} invariant: c = 0 gives (a, b), c = 1 gives (b, a) — a branch-free swap.
    Note both assigns read the ORIGINAL a and b (the Rust default uses a temporary), so
    the sequencing in the `do` block is faithful.
    WHY NEEDED: fills the `conditional_swap` slot of instance records in Funs.lean that
    use the trait default (e.g. FieldElement51's). -/
@[rust_fun "subtle::ConditionallySelectable::conditional_swap"]
def subtle.ConditionallySelectable.conditional_swap.default
  {Self : Type} (ConditionallySelectableInst : subtle.ConditionallySelectable
  Self) (a b : Self) (choice : subtle.Choice) : Result (Self × Self) := do
  let a1 ← ConditionallySelectableInst.conditional_assign a b choice
  let b1 ← ConditionallySelectableInst.conditional_assign b a choice
  ok (a1, b1)

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_select]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 513:12-513:77
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_select]

    MODEL: `a` if choice = 0, else `b`. The Rust mask trick
    `a ^ (-(choice as i64) as u64 & (a ^ b))` agrees with this on the Choice
    invariant {0,1} (mask = 0 or all-ones).

    subtle crate: `impl ConditionallySelectable for u64` — branch-free 64-bit select.
    ASCII:  conditional_select(a, b, c) = ok (if c = 0 then a else b)
    Soundness of the collapse to if-then-else: mask = (0 - c) mod 2^64 is 0 when c = 0 and
    2^64 - 1 (all ones) when c = 1; then
        a XOR (0          AND (a XOR b)) = a XOR 0         = a, and
        a XOR ((2^64 - 1) AND (a XOR b)) = a XOR (a XOR b) = b.
    Every Choice produced by the models in this file is 0 or 1, so the model is exact on
    all reachable executions.
    WHY NEEDED: `FieldElement51`'s `conditional_select` (backend/serial/u64/field.rs:
    226-238, translated in Funs.lean) applies this to each of the 5 limbs; `sqrt_ratio_i`
    correctness rests on it. Pinned as `u64_conditional_select_spec` in
    Proofs/Basic.lean. -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_select"]
def U64.Insts.SubtleConditionallySelectable.conditional_select
  (a b : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice.val = 0 then a else b)

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_assign]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 521:12-521:74
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign]

    MODEL: keep `self` if choice = 0, else take `other` (same mask trick).

    subtle crate: `impl ConditionallySelectable for u64`, overridden `conditional_assign`.
    ASCII:  conditional_assign(self, other, c) = ok (if c = 0 then self else other)
    Same mask argument as `conditional_select` above (`*self ^= mask & (*self ^ *other)`),
    exact on the {0,1} Choice invariant; the `&mut self` becomes the returned value.
    WHY NEEDED: `FieldElement51::conditional_assign` (backend/serial/u64/field.rs:248-254)
    updates each limb with this; `sqrt_ratio_i` (src/field.rs) uses it twice to fix the
    sign of the square root. Pinned as `u64_conditional_assign_spec` in
    Proofs/Basic.lean. -/
@[rust_fun
  "subtle::{subtle::ConditionallySelectable<u64>}::conditional_assign"]
def U64.Insts.SubtleConditionallySelectable.conditional_assign
  (self other : Std.U64) (choice : subtle.Choice) : Result Std.U64 :=
  ok (if choice.val = 0 then self else other)

/-- [subtle::{impl subtle::ConditionallySelectable for u64}::conditional_swap]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 529:12-529:75
    Name pattern: [subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap]

    MODEL: swap iff choice ≠ 0 (same mask trick, applied to both sides).

    subtle crate: `impl ConditionallySelectable for u64`, overridden `conditional_swap`.
    ASCII:  conditional_swap(a, b, c) = ok (if c = 0 then (a, b) else (b, a))
    Rust computes t = mask & (a ^ b) once and does `a ^= t; b ^= t` — with mask = 0 this
    leaves both unchanged, with mask = all-ones it exchanges them; exact on c in {0,1}.
    The two `&mut` arguments come back as the returned pair.
    WHY NEEDED: `FieldElement51::conditional_swap` (backend/serial/u64/field.rs:240-246)
    swaps each limb pair with this; kept modeled so the FieldElement51 instance record in
    Funs.lean is fully populated even though the field theorem itself never swaps. -/
@[rust_fun "subtle::{subtle::ConditionallySelectable<u64>}::conditional_swap"]
def U64.Insts.SubtleConditionallySelectable.conditional_swap
  (a b : Std.U64) (choice : subtle.Choice) : Result (Std.U64 × Std.U64) :=
  ok (if choice.val = 0 then (a, b) else (b, a))

-- ──────────────────────────────────────────────────────────────────────────────────────────
-- Deliberately opaque curve25519 item (the one function extracted WITHOUT a body).
-- ──────────────────────────────────────────────────────────────────────────────────────────

/-- [curve25519::field::{curve25519::backend::serial::u64::field::FieldElement51}::internal_invert_batch]:
    Source: 'curve25519/solana-ed25519/src/field.rs', lines 195:4-229:5

    AXIOM (deliberate): extracted opaque via charon `--opaque`. Dead code under
    the extraction feature set (its only caller `invert_batch_alloc` is
    alloc-gated); its iterator `rev/zip` loops have no Aeneas model. Give it a
    model here if batch inversion ever becomes a verification target.

    Rust: `FieldElement51::internal_invert_batch(inputs: &mut [FieldElement],
    scratch: &mut [FieldElement])`, curve25519/solana-ed25519/src/field.rs:195-229 —
    Montgomery's batch-inversion trick (one `invert` plus 3(n-1) multiplications inverts n
    elements). The two `&mut` slices come back as the returned pair (the functional
    encoding of mutation). The axiom asserts only that a function of this type exists; no
    equation about its behavior is postulated, so it cannot contribute to any field-theorem
    proof — and indeed it is NOT in the axiom cone of
    CurveFieldProofs.fieldImplementation (checked via #print axioms). -/
axiom field.FieldElement51.internal_invert_batch
  :
  Slice backend.serial.u64.field.FieldElement51 → Slice
    backend.serial.u64.field.FieldElement51 → Result ((Slice
    backend.serial.u64.field.FieldElement51) × (Slice
    backend.serial.u64.field.FieldElement51))

/-! ## Externals added by the point-arithmetic extraction (Tier-1 Edwards work)

The unified extraction (field + curve_models + edwards) declares these extra
external items. ALL of them are outside the bodies verified by the proofs:
either deliberately opaqued machinery (scalar multiplication backends, backend
dispatch, decompress steps, iterator Sum) or derive/trait plumbing (Hash,
Eq-derive helpers, Debug formatting, range-Step methods). They are kept as
AXIOMS (no models needed); none may enter the dependency cone of the verified
theorems — checked by #print axioms in the proof files. -/

/-- [core::array::{impl core::hash::Hash for [T; N]}::hash]:
    Source: '/rustc/library/core/src/array/mod.rs', lines 349:4-349:50
    Name pattern: [core::array::{core::hash::Hash<[@T; @N]>}::hash]
    Visibility: public -/
@[rust_fun "core::array::{core::hash::Hash<[@T; @N]>}::hash"]
axiom Array.Insts.CoreHashHash.hash
  {T : Type} {H : Type} {N : Std.Usize} (hashHashInst : core.hash.Hash T)
  (hashHasherInst : core.hash.Hasher H) :
  Array T N → H → Result H

/-- [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish]:
    Source: '/rustc/library/core/src/fmt/mod.rs', lines 2473:4-2480:15
    Name pattern: [core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish]
    Visibility: public -/
@[rust_fun "core::fmt::{core::fmt::Formatter<'a>}::debug_struct_field2_finish"]
axiom core.fmt.Formatter.debug_struct_field2_finish
  :
  core.fmt.Formatter → Str → Str → Dyn (fun _dyn => core.fmt.Debug _dyn)
    → Str → Dyn (fun _dyn => core.fmt.Debug _dyn) → Result
    ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter)

/-- [core::hash::impls::{impl core::hash::Hash for u8}::hash]:
    Source: '/rustc/library/core/src/hash/mod.rs', lines 812:16-812:56
    Name pattern: [core::hash::impls::{core::hash::Hash<u8>}::hash]
    Visibility: public -/
@[rust_fun "core::hash::impls::{core::hash::Hash<u8>}::hash"]
axiom U8.Insts.CoreHashHash.hash
  {H : Type} (HasherInst : core.hash.Hasher H) : Std.U8 → H → Result H

/-- [core::iter::range::{impl core::iter::range::Step for u32}::backward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 290:16-290:74
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::backward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::backward_checked"]
axiom U32.Insts.CoreIterRangeStep.backward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::forward_checked]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 282:16-282:73
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::forward_checked]
    Visibility: public -/
@[rust_fun
  "core::iter::range::{core::iter::range::Step<u32>}::forward_checked"]
axiom U32.Insts.CoreIterRangeStep.forward_checked
  : Std.U32 → Std.Usize → Result (Option Std.U32)

/-- [core::iter::range::{impl core::iter::range::Step for u32}::steps_between]:
    Source: '/rustc/library/core/src/iter/range.rs', lines 271:16-271:84
    Name pattern: [core::iter::range::{core::iter::range::Step<u32>}::steps_between]
    Visibility: public -/
@[rust_fun "core::iter::range::{core::iter::range::Step<u32>}::steps_between"]
axiom U32.Insts.CoreIterRangeStep.steps_between
  : Std.U32 → Std.U32 → Result (Std.Usize × (Option Std.Usize))

/-- [subtle::{subtle::Choice}::unwrap_u8]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 133:4-133:33
    Name pattern: [subtle::{subtle::Choice}::unwrap_u8]
    Visibility: public -/
@[rust_fun "subtle::{subtle::Choice}::unwrap_u8"]
axiom subtle.Choice.unwrap_u8 : subtle.Choice → Result Std.U8

/-- [subtle::{impl core::ops::bit::BitAnd<subtle::Choice, subtle::Choice> for subtle::Choice}::bitand]:
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/subtle-2.6.1/src/lib.rs', lines 162:4-162:42
    Name pattern: [subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand]
    Visibility: public -/
@[rust_fun
  "subtle::{core::ops::bit::BitAnd<subtle::Choice, subtle::Choice, subtle::Choice>}::bitand"]
axiom subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand
  : subtle.Choice → subtle.Choice → Result subtle.Choice

/-- [curve25519::backend::serial::scalar_mul::variable_base::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/scalar_mul/variable_base.rs', lines 11:0-48:1 -/
axiom backend.serial.scalar_mul.variable_base.mul
  : edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::serial::scalar_mul::vartime_double_base::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/scalar_mul/vartime_double_base.rs', lines 23:0-72:1
    Visibility: public -/
axiom backend.serial.scalar_mul.vartime_double_base.mul
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar → Result
    edwards.EdwardsPoint

/-- [curve25519::backend::serial::scalar_mul::vartime_triple_base::mul_128_128_256]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/scalar_mul/vartime_triple_base.rs', lines 48:0-148:1
    Visibility: public -/
axiom backend.serial.scalar_mul.vartime_triple_base.mul_128_128_256
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar →
    edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::variable_base::spec_avx2::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/variable_base.rs', lines 3:0-3:68
    Visibility: public -/
axiom backend.vector.scalar_mul.variable_base.spec_avx2.mul
  : edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::vartime_double_base::spec_avx2::mul]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/vartime_double_base.rs', lines 14:0-14:68
    Visibility: public -/
axiom backend.vector.scalar_mul.vartime_double_base.spec_avx2.mul
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar → Result
    edwards.EdwardsPoint

/-- [curve25519::backend::vector::scalar_mul::vartime_triple_base::spec_avx2::mul_128_128_256]:
    Source: 'curve25519/solana-ed25519/src/backend/vector/scalar_mul/vartime_triple_base.rs', lines 10:0-10:68
    Visibility: public -/
axiom backend.vector.scalar_mul.vartime_triple_base.spec_avx2.mul_128_128_256
  :
  scalar.Scalar → edwards.EdwardsPoint → scalar.Scalar →
    edwards.EdwardsPoint → scalar.Scalar → Result edwards.EdwardsPoint

/-- [curve25519::backend::get_selected_backend]:
    Source: 'curve25519/solana-ed25519/src/backend.rs', lines 53:0-64:1 -/
axiom backend.get_selected_backend : Result backend.BackendKind

/-- [curve25519::edwards::affine::{impl core::cmp::Eq for curve25519::edwards::affine::AffinePoint}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 53:0-53:26
    Visibility: public -/
axiom edwards.affine.AffinePoint.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.affine.AffinePoint → Result Unit

/-- [curve25519::edwards::{impl core::cmp::Eq for curve25519::edwards::CompressedEdwardsY}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 183:0-183:33
    Visibility: public -/
axiom edwards.CompressedEdwardsY.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.CompressedEdwardsY → Result Unit

/-- [curve25519::edwards::decompress::step_2]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 240:4-257:5 -/
axiom edwards.decompress.step_2
  :
  edwards.CompressedEdwardsY → backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 →
    backend.serial.u64.field.FieldElement51 → Result edwards.EdwardsPoint

/-- [curve25519::edwards::{curve25519::edwards::CompressedEdwardsY}::from_slice]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 423:4-425:5
    Visibility: public -/
axiom edwards.CompressedEdwardsY.from_slice
  :
  Slice Std.U8 → Result (core.result.Result edwards.CompressedEdwardsY
    core.array.TryFromSliceError)

/-- [curve25519::edwards::{impl subtle::ConditionallySelectable for curve25519::edwards::EdwardsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 486:0-495:1
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    (edwards.EdwardsPoint × edwards.EdwardsPoint)

/-- [curve25519::edwards::{impl core::cmp::Eq for curve25519::edwards::EdwardsPoint}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 520:0-520:27
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.CoreCmpEq.assert_fields_are_eq
  : edwards.EdwardsPoint → Result Unit

/-- [curve25519::edwards::{impl core::iter::traits::accum::Sum<T> for curve25519::edwards::EdwardsPoint}::sum]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 829:4-834:5
    Visibility: public -/
axiom edwards.EdwardsPoint.Insts.CoreIterTraitsAccumSum.sum
  {T : Type} {I : Type} (coreborrowBorrowTEdwardsPointInst : core.borrow.Borrow
  T edwards.EdwardsPoint) (coreitertraitsiteratorIteratorInst :
  core.iter.traits.iterator.Iterator I T) :
  I → Result edwards.EdwardsPoint

-- ──────────────────────────────────────────────────────────────────────────────────────────
-- Externals added by the 2026-06-12 regeneration that included the CURVE modules
-- (curve_models.rs / edwards.rs / window.rs closure). Synced verbatim from
-- FunsExternal_Template.lean per the documented workflow (see extract.sh): after
-- regeneration, new template skeletons must be mirrored here or Funs.lean cannot
-- elaborate. All six are kept as AXIOMS (policy case (b) of the header): they are
-- constant-time swap/assign helpers and a derive(Eq) marker assertion, and nothing
-- in the proof cone (field layer, point denotation layer) depends on their behavior.
-- ──────────────────────────────────────────────────────────────────────────────────────────

/-- [curve25519::backend::serial::curve_models::{impl subtle::ConditionallySelectable for curve25519::backend::serial::curve_models::ProjectiveNielsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/curve_models.rs', lines 295:0-311:1
    Visibility: public

    AXIOM: per-field constant-time swap of two ProjectiveNielsPoints; only reachable
    from scalar-mul table lookups, which are themselves opaque here. No proof in the
    field or point-denotation cone depends on it. -/
axiom
  backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.ProjectiveNielsPoint →
    backend.serial.curve_models.ProjectiveNielsPoint → subtle.Choice →
    Result (backend.serial.curve_models.ProjectiveNielsPoint ×
    backend.serial.curve_models.ProjectiveNielsPoint)

/-- [curve25519::backend::serial::curve_models::{impl subtle::ConditionallySelectable for curve25519::backend::serial::curve_models::AffineNielsPoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/backend/serial/curve_models.rs', lines 313:0-327:1
    Visibility: public

    AXIOM: same situation as the ProjectiveNielsPoint swap above. -/
axiom
  backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  backend.serial.curve_models.AffineNielsPoint →
    backend.serial.curve_models.AffineNielsPoint → subtle.Choice → Result
    (backend.serial.curve_models.AffineNielsPoint ×
    backend.serial.curve_models.AffineNielsPoint)

/-- [curve25519::edwards::affine::{impl subtle::ConditionallySelectable for curve25519::edwards::affine::AffinePoint}::conditional_swap]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 23:0-30:1
    Visibility: public

    AXIOM: constant-time swap of two AffinePoints; unused by any current proof. -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_swap
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result (edwards.affine.AffinePoint × edwards.affine.AffinePoint)

/-- [curve25519::edwards::affine::{impl subtle::ConditionallySelectable for curve25519::edwards::affine::AffinePoint}::conditional_assign]:
    Source: 'curve25519/solana-ed25519/src/edwards/affine.rs', lines 23:0-30:1
    Visibility: public

    AXIOM: constant-time assign for AffinePoint; unused by any current proof. -/
axiom
  edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.affine.AffinePoint → edwards.affine.AffinePoint → subtle.Choice
    → Result edwards.affine.AffinePoint

/-- [curve25519::edwards::{impl subtle::ConditionallySelectable for curve25519::edwards::EdwardsPoint}::conditional_assign]:
    Source: 'curve25519/solana-ed25519/src/edwards.rs', lines 486:0-495:1
    Visibility: public

    AXIOM: constant-time assign for EdwardsPoint (sibling of the conditional_swap
    axiom already modeled above); unused by any current proof. -/
axiom
  edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_assign
  :
  edwards.EdwardsPoint → edwards.EdwardsPoint → subtle.Choice → Result
    edwards.EdwardsPoint

/-- [curve25519::field::{impl core::cmp::Eq for curve25519::backend::serial::u64::field::FieldElement51}::assert_fields_are_eq]:
    Source: 'curve25519/solana-ed25519/src/field.rs', lines 49:0-49:27
    Visibility: public

    AXIOM: the derive(Eq) marker assertion for FieldElement51 (the Rust body is empty);
    same modeling as the three existing assert_fields_are_eq axioms above. -/
axiom
  backend.serial.u64.field.FieldElement51.Insts.CoreCmpEq.assert_fields_are_eq
  : backend.serial.u64.field.FieldElement51 → Result Unit
