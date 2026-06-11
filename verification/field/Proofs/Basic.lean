/- First proofs over the Aeneas-generated field model (CurveField).

   These establish the proof pattern for this workspace:
   - pin down the semantics of the hand-written external models
     (gen/CurveField/FunsExternal.lean) as reusable simp lemmas, and
   - prove first sanity facts about the generated code itself.

   The real verification targets (limb-bound invariants, add/sub/mul/square
   correctness vs. ℤ/(2²⁵⁵-19), panic-freedom of the carry chains, and the
   sqrt_ratio_i specification) build on these — see ../README.md. -/
import CurveField.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open curve25519

namespace CurveFieldProofs

/-! ## Semantics of the external models (subtle) -/

/-- `Choice::from(u8)` is the identity (the Rust `black_box` is a barrier). -/
@[simp]
theorem choice_from_u8_spec (b : Std.U8) :
    subtle.Choice.Insts.CoreConvertFromU8.from b = ok b := rfl

/-- `bool::from(Choice)` tests non-zeroness. -/
@[simp]
theorem bool_from_choice_spec (c : subtle.Choice) :
    Bool.Insts.CoreConvertFromChoice.from c = ok (c.val != 0) := rfl

/-- `u64::conditional_select(a, b, c)` keeps `a` iff `c = 0`. -/
@[simp]
theorem u64_conditional_select_spec (a b : Std.U64) (c : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b c
      = ok (if c.val = 0 then a else b) := rfl

/-- `u64::conditional_assign(self, other, c)` keeps `self` iff `c = 0`. -/
@[simp]
theorem u64_conditional_assign_spec (a b : Std.U64) (c : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_assign a b c
      = ok (if c.val = 0 then a else b) := rfl

/-- `u8::ct_eq` decides equality. -/
@[simp]
theorem u8_ct_eq_spec (a b : Std.U8) :
    U8.Insts.SubtleConstantTimeEq.ct_eq a b
      = ok (if a = b then 1#u8 else 0#u8) := rfl

/-! ## First facts about the generated field code -/

/-- `FieldElement51::ZERO` is the all-zero limb array. -/
theorem zero_spec :
    backend.serial.u64.field.FieldElement51.ZERO
      = ok (Array.repeat 5#usize 0#u64) := by
  unfold backend.serial.u64.field.FieldElement51.ZERO
    backend.serial.u64.field.FieldElement51.from_limbs
  rfl

/-- `<FieldElement51 as Default>::default()` is `ZERO`. -/
theorem default_eq_zero :
    backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault.default
      = backend.serial.u64.field.FieldElement51.ZERO := by
  unfold
    backend.serial.u64.field.FieldElement51.Insts.CoreDefaultDefault.default
  rfl

/-- `FieldElement51::from_limbs` never fails. -/
@[simp]
theorem from_limbs_spec (limbs : Array Std.U64 5#usize) :
    backend.serial.u64.field.FieldElement51.from_limbs limbs = ok limbs := rfl

end CurveFieldProofs
