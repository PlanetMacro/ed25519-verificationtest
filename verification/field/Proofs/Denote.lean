/- Denotation layer: interpret the transpiled `FieldElement51` into 𝔽_p,
   p = 2²⁵⁵ − 19, and define the limb-bound invariant.

   NOTE: nothing in Proofs/ modifies the transpiled code (gen/CurveField/);
   we only define functions *about* it and prove equivalences. -/
import CurveField.Funs
open Aeneas Aeneas.Std Result
open curve25519

namespace CurveFieldProofs

/-- The field characteristic p = 2²⁵⁵ − 19. -/
def P : ℕ := 2^255 - 19

/-- The mathematical field 𝔽_p (mathlib's `ZMod P`). -/
abbrev Fp := ZMod P

/-- Short alias for the transpiled field-element type ([u64; 5]). -/
abbrev Fe := backend.serial.u64.field.FieldElement51

/-! Short aliases for the transpiled operations (the Aeneas names are long).
    These are definitionally the generated functions — `rfl`-equal. -/
abbrev fe_add :=
  Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
abbrev fe_sub :=
  Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
abbrev fe_mul :=
  Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51.mul
abbrev fe_neg := backend.serial.u64.field.FieldElement51.negate
abbrev fe_reduce := backend.serial.u64.field.FieldElement51.reduce
abbrev fe_square := backend.serial.u64.field.FieldElement51.square
abbrev fe_pow2k := backend.serial.u64.field.FieldElement51.pow2k
abbrev fe_invert := field.FieldElement51.invert
abbrev fe_zero := backend.serial.u64.field.FieldElement51.ZERO
abbrev fe_one := backend.serial.u64.field.FieldElement51.ONE
abbrev fe_minus_one := backend.serial.u64.field.FieldElement51.MINUS_ONE

/-- Every `Fe` is a 5-element list of u64 limbs. -/
theorem Fe.exists_limbs (a : Fe) :
    ∃ a0 a1 a2 a3 a4 : U64, (↑a : List U64) = [a0, a1, a2, a3, a4] := by
  have h : (↑a : List U64).length = 5 := by
    have := a.property
    simp_all
  match hl : (↑a : List U64) with
  | [a0, a1, a2, a3, a4] => exact ⟨a0, a1, a2, a3, a4, rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] => simp [hl] at h
  | _::_::_::_::_::_::_ => simp [hl] at h

/-- Value of a limb vector as a natural number (radix 2⁵¹). -/
def limbsVal (a0 a1 a2 a3 a4 : U64) : ℕ :=
  a0.val + 2^51 * a1.val + 2^102 * a2.val + 2^153 * a3.val + 2^204 * a4.val

/-- Value of a field element as a natural number. -/
def feVal (a : Fe) : ℕ :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3, a4] => limbsVal a0 a1 a2 a3 a4
  | _ => 0

@[simp]
theorem feVal_eq (a : Fe) (a0 a1 a2 a3 a4 : U64)
    (h : (↑a : List U64) = [a0, a1, a2, a3, a4]) :
    feVal a = limbsVal a0 a1 a2 a3 a4 := by
  simp [feVal, h]

/-- The denotation ⟪a⟫ : 𝔽_p of a field element. -/
def denote (a : Fe) : Fp := (feVal a : Fp)

/- (⟪·⟫ rather than ⟦·⟧, which collides with `Quotient.mk`.) -/
notation "⟪" a "⟫" => denote a

/-- Limb-bound invariant: all limbs < `c`. Operations require/provide:
    `reduce`/`mul`/`square` outputs satisfy `Bnd · (2^52)`;
    `mul`/`square`/`sub`/`neg` inputs require `Bnd · (2^54)`. -/
def Bnd (a : Fe) (c : ℕ) : Prop :=
  match (↑a : List U64) with
  | [a0, a1, a2, a3, a4] =>
    a0.val < c ∧ a1.val < c ∧ a2.val < c ∧ a3.val < c ∧ a4.val < c
  | _ => False

@[simp]
theorem Bnd_eq (a : Fe) (a0 a1 a2 a3 a4 : U64) (c : ℕ)
    (h : (↑a : List U64) = [a0, a1, a2, a3, a4]) :
    Bnd a c ↔
      (a0.val < c ∧ a1.val < c ∧ a2.val < c ∧ a3.val < c ∧ a4.val < c) := by
  simp [Bnd, h]

theorem Bnd.mono {a : Fe} {c c' : ℕ} (h : Bnd a c) (hcc : c ≤ c') : Bnd a c' := by
  obtain ⟨a0, a1, a2, a3, a4, hl⟩ := Fe.exists_limbs a
  rw [Bnd_eq a a0 a1 a2 a3 a4 c hl] at h
  rw [Bnd_eq a a0 a1 a2 a3 a4 c' hl]
  omega

/-! ## Basic facts about P -/

theorem P_pos : 0 < P := by norm_num [P]

theorem two_pow_255_eq :
    ((2^255 : ℕ) : Fp) = (19 : Fp) := by
  have h : ((P : ℕ) : Fp) = 0 := ZMod.natCast_self P
  have : (2^255 : ℕ) = P + 19 := by norm_num [P]
  rw [this]
  push_cast [h]
  ring

end CurveFieldProofs
