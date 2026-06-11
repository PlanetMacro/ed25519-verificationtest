/- Spec for the transpiled `FieldElement51::reduce`:
   it never panics, its output limbs are < 2⁵¹ + 19·2¹³ (⊂ 2⁵²), and it
   preserves the value modulo p (exact Nat relation: it subtracts (l4 ≫ 51)·p). -/
import Proofs.Denote
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-- The mask constant evaluates to 2⁵¹ − 1. -/
@[step]
theorem reduce_mask_spec :
    backend.serial.u64.field.FieldElement51.reduce.LOW_51_BIT_MASK
      ⦃ m => m.val = 2^51 - 1 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.reduce.LOW_51_BIT_MASK
  step*

/-- Convert `&&& (2^51-1)` and `>>> 51` on `ℕ` to `%`/`/` so `omega` can reason.
    Stated with the *literal* (2251799813685247 = 2⁵¹−1) since simp normalizes
    `2^51 - 1` to it before these lemmas get a chance to fire. -/
@[simp, scalar_tac_simps]
theorem nat_and_mask (n : ℕ) : n &&& 2251799813685247 = n % 2251799813685248 := by
  have := Nat.and_two_pow_sub_one_eq_mod n 51
  norm_num at this
  simpa using this

@[simp, scalar_tac_simps]
theorem nat_shift_div (n : ℕ) : n >>> 51 = n / 2251799813685248 := by
  simp [Nat.shiftRight_eq_div_pow]

/-- `reduce` spec: total (no panic), output bounded, value preserved mod p. -/
theorem reduce_spec (l : Fe) (l0 l1 l2 l3 l4 : U64)
    (hl : (↑l : List U64) = [l0, l1, l2, l3, l4]) :
    fe_reduce l ⦃ r =>
      Bnd r (2^51 + 19 * 2^13) ∧
      feVal r + P * (l4.val / 2^51) = feVal l ⦄ := by
  unfold fe_reduce backend.serial.u64.field.FieldElement51.reduce
  step* by (subst_vars
            try simp [Array.set_val_eq, *]
            try scalar_tac)
  -- Final postcondition: normalize the set-chain + all value equations to
  -- %/÷ arithmetic over the input limbs (simp_all also uses the inaccessible
  -- step*-generated hypotheses), then close with omega.
  simp_all [Array.set_val_eq, P, limbsVal, Bnd, feVal]
  scalar_tac

end CurveFieldProofs
