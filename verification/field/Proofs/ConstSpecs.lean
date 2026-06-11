/- Specs for the transpiled field constants:
   `ZERO`, `ONE`, `MINUS_ONE` (FieldElement51) and `SQRT_M1` (constants).
   Each constant evaluates totally (no panic), satisfies the limb-bound
   invariant `Bnd`, and denotes the expected element of 𝔽_p. -/
import Proofs.Denote
open Aeneas Aeneas.Std Result
open curve25519

namespace CurveFieldProofs

/-! ## Casting `P - 1` into 𝔽_p gives `-1` -/

theorem natCast_P_sub_one : ((P - 1 : ℕ) : Fp) = -1 := by
  have h1 : (1 : ℕ) ≤ P := by norm_num [P]
  rw [Nat.cast_sub h1, ZMod.natCast_self]
  push_cast
  ring

/-! ## ZERO -/

theorem zero_spec :
    fe_zero ⦃ z =>
      (↑z : List U64) = [0#u64, 0#u64, 0#u64, 0#u64, 0#u64] ∧
      Bnd z (2^51) ∧ denote z = 0 ⦄ := by
  unfold fe_zero backend.serial.u64.field.FieldElement51.ZERO
    backend.serial.u64.field.FieldElement51.from_limbs
  simp [Bnd, denote, feVal, limbsVal, Array.repeat, List.replicate]

/-! ## ONE -/

theorem one_spec : fe_one ⦃ o => Bnd o (2^51) ∧ denote o = 1 ⦄ := by
  unfold fe_one backend.serial.u64.field.FieldElement51.ONE
    backend.serial.u64.field.FieldElement51.from_limbs
  simp [Bnd, denote, feVal, limbsVal, Array.make]

/-! ## MINUS_ONE -/

theorem minus_one_spec : fe_minus_one ⦃ m => Bnd m (2^52) ∧ denote m = -1 ⦄ := by
  unfold fe_minus_one backend.serial.u64.field.FieldElement51.MINUS_ONE
    backend.serial.u64.field.FieldElement51.from_limbs
  -- simp discharges the Bnd conjunct and evaluates `feVal` to the literal
  -- 2²⁵⁵ − 20 = P − 1; the remaining goal is `(P − 1 : 𝔽_p) = -1`.
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  have h := natCast_P_sub_one
  have hc : (P - 1 : ℕ) =
      57896044618658097711785492504343953926634992332820282019728792003956564819948 := by
    norm_num [P]
  rw [hc] at h
  exact_mod_cast h

/-! ## SQRT_M1 -/

theorem sqrt_m1_spec :
    backend.serial.u64.constants.SQRT_M1 ⦃ s => Bnd s (2^52) ∧ denote s * denote s = -1 ⦄ := by
  unfold backend.serial.u64.constants.SQRT_M1
    backend.serial.u64.field.FieldElement51.from_limbs
  -- simp discharges the Bnd conjunct and evaluates `feVal` to the literal N
  -- (the 255-bit value of the SQRT_M1 limbs); the remaining goal is
  -- `(N : 𝔽_p) * (N : 𝔽_p) = -1`.
  simp [Bnd, denote, feVal, limbsVal, Array.make]
  -- N² ≡ P − 1 (mod P), checked by literal arithmetic on ℕ.
  have hmod :
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 *
        19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ))
        % P = P - 1 := by
    norm_num [P]
  have key :
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ) : Fp) *
      ((19681161376707505956807079304988542015446066515923890162744021073123829784752 : ℕ) : Fp)
        = -1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, hmod, natCast_P_sub_one]
  exact_mod_cast key

end CurveFieldProofs
