/- Spec for the transpiled `FieldElement51::square`/`pow2k` (radix-2⁵¹ squaring,
   19-folded): no panic under the 2⁵⁴ invariant, output limbs < 2⁵¹ + 2¹³, and
   the denotation is `⟪a⟫ ^ (2^k)` (resp. `⟪a⟫ * ⟪a⟫` for `square`).

   The body proof mirrors Proofs/MulSpec.lean step by step (let* + named posts,
   interleaved bound facts so every overflow side condition is linear); the
   `pow2k` loop is handled by fuel induction on `k.val` using `loop_step` from
   Proofs/AddSpec.lean. -/
import Proofs.MulSpec
import Proofs.AddSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- The u128 widening product `pow2k.m(x, y) = (x as u128) * (y as u128)`. -/
@[step]
theorem pow2k_m_spec (x y : U64) :
    backend.serial.u64.field.FieldElement51.pow2k.m x y
      ⦃ z => z.val = x.val * y.val ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.pow2k.m
  have hx : x.val < 2^64 := x.hBounds
  have hy : y.val < 2^64 := y.hBounds
  have hxy : x.val * y.val < 2^128 := by
    calc x.val * y.val < 2^64 * 2^64 := Nat.mul_lt_mul'' hx hy
      _ = 2^128 := by norm_num
  step* by dis

/-- The mask constant in `pow2k` evaluates to 2⁵¹ − 1. -/
@[step]
theorem pow2k_mask_spec :
    backend.serial.u64.field.FieldElement51.pow2k.LOW_51_BIT_MASK
      ⦃ m => m.val = 2251799813685247 ⦄ := by
  unfold backend.serial.u64.field.FieldElement51.pow2k.LOW_51_BIT_MASK
  step*

/-- One iteration of the `pow2k` loop body: it squares the field element
    (limbs < 2⁵¹ + 2¹³ afterwards) and decrements `k`, breaking iff `k = 1`. -/
theorem pow2k_body_spec (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    backend.serial.u64.field.FieldElement51.pow2k_loop.body k a ⦃ cf =>
      (k.val = 1 ∧ ∃ r : Fe, cf = .done r ∧ Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫) ∨
      (2 ≤ k.val ∧ ∃ (k1 : U32) (r : Fe), cf = .cont (k1, r) ∧ k1.val = k.val - 1 ∧
        Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫) ⦄ := by
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  unfold backend.serial.u64.field.FieldElement51.pow2k_loop.body
  -- limb loads + 19·a3, 19·a4 precomputations
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec by dis
  have he_i : i = x3 := by simp [i_post, ha]
  have hv_i : i.val < 2^54 := by rw [he_i]; omega
  let* ⟨ a3_19, a3_19_post ⟩ ← U64.mul_spec by dis
  have hv_a3_19 : a3_19.val < 19 * 2^54 := by rw [a3_19_post]; omega
  let* ⟨ i1, i1_post ⟩ ← Array.index_usize_spec by dis
  have he_i1 : i1 = x4 := by simp [i1_post, ha]
  have hv_i1 : i1.val < 2^54 := by rw [he_i1]; omega
  let* ⟨ a4_19, a4_19_post ⟩ ← U64.mul_spec by dis
  have hv_a4_19 : a4_19.val < 19 * 2^54 := by rw [a4_19_post]; omega
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec by dis
  have he_i2 : i2 = x0 := by simp [i2_post, ha]
  have hv_i2 : i2.val < 2^54 := by rw [he_i2]; omega
  -- c0 = a0·a0 + 2·(a1·(19·a4) + a2·(19·a3))
  let* ⟨ i3, i3_post ⟩ ← pow2k_m_spec by dis
  have hv_i3 : i3.val < 2^108 := by
    rw [i3_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i2; omega
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec by dis
  have he_i4 : i4 = x1 := by simp [i4_post, ha]
  have hv_i4 : i4.val < 2^54 := by rw [he_i4]; omega
  let* ⟨ i5, i5_post ⟩ ← pow2k_m_spec by dis
  have hv_i5 : i5.val < 2^54 * (19 * 2^54) := by
    rw [i5_post]; have := Nat.mul_lt_mul'' hv_i4 hv_a4_19; omega
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec by dis
  have he_i6 : i6 = x2 := by simp [i6_post, ha]
  have hv_i6 : i6.val < 2^54 := by rw [he_i6]; omega
  let* ⟨ i7, i7_post ⟩ ← pow2k_m_spec by dis
  have hv_i7 : i7.val < 2^54 * (19 * 2^54) := by
    rw [i7_post]; have := Nat.mul_lt_mul'' hv_i6 hv_a3_19; omega
  let* ⟨ i8, i8_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i8 : i8.val < 38 * 2^108 := by rw [i8_post]; omega
  let* ⟨ i9, i9_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i9 : i9.val < 76 * 2^108 := by rw [i9_post]; omega
  let* ⟨ c0, c0_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c0 : c0.val < 77 * 2^108 := by rw [c0_post]; omega
  -- c1 = a3·(19·a3) + 2·(a0·a1 + a2·(19·a4))
  let* ⟨ i10, i10_post ⟩ ← pow2k_m_spec by dis
  have hv_i10 : i10.val < 2^54 * (19 * 2^54) := by
    rw [i10_post]; have := Nat.mul_lt_mul'' hv_i hv_a3_19; omega
  let* ⟨ i11, i11_post ⟩ ← pow2k_m_spec by dis
  have hv_i11 : i11.val < 2^108 := by
    rw [i11_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i4; omega
  let* ⟨ i12, i12_post ⟩ ← pow2k_m_spec by dis
  have hv_i12 : i12.val < 2^54 * (19 * 2^54) := by
    rw [i12_post]; have := Nat.mul_lt_mul'' hv_i6 hv_a4_19; omega
  let* ⟨ i13, i13_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i13 : i13.val < 20 * 2^108 := by rw [i13_post]; omega
  let* ⟨ i14, i14_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i14 : i14.val < 40 * 2^108 := by rw [i14_post]; omega
  let* ⟨ c1, c1_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c1 : c1.val < 59 * 2^108 := by rw [c1_post]; omega
  -- c2 = a1·a1 + 2·(a0·a2 + a4·(19·a3))
  let* ⟨ i15, i15_post ⟩ ← pow2k_m_spec by dis
  have hv_i15 : i15.val < 2^108 := by
    rw [i15_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i4; omega
  let* ⟨ i16, i16_post ⟩ ← pow2k_m_spec by dis
  have hv_i16 : i16.val < 2^108 := by
    rw [i16_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i6; omega
  let* ⟨ i17, i17_post ⟩ ← pow2k_m_spec by dis
  have hv_i17 : i17.val < 2^54 * (19 * 2^54) := by
    rw [i17_post]; have := Nat.mul_lt_mul'' hv_i1 hv_a3_19; omega
  let* ⟨ i18, i18_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i18 : i18.val < 20 * 2^108 := by rw [i18_post]; omega
  let* ⟨ i19, i19_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i19 : i19.val < 40 * 2^108 := by rw [i19_post]; omega
  let* ⟨ c2, c2_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c2 : c2.val < 41 * 2^108 := by rw [c2_post]; omega
  -- c3 = a4·(19·a4) + 2·(a0·a3 + a1·a2)
  let* ⟨ i20, i20_post ⟩ ← pow2k_m_spec by dis
  have hv_i20 : i20.val < 2^54 * (19 * 2^54) := by
    rw [i20_post]; have := Nat.mul_lt_mul'' hv_i1 hv_a4_19; omega
  let* ⟨ i21, i21_post ⟩ ← pow2k_m_spec by dis
  have hv_i21 : i21.val < 2^108 := by
    rw [i21_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i; omega
  let* ⟨ i22, i22_post ⟩ ← pow2k_m_spec by dis
  have hv_i22 : i22.val < 2^108 := by
    rw [i22_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i6; omega
  let* ⟨ i23, i23_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i23 : i23.val < 2 * 2^108 := by rw [i23_post]; omega
  let* ⟨ i24, i24_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i24 : i24.val < 4 * 2^108 := by rw [i24_post]; omega
  let* ⟨ c3, c3_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c3 : c3.val < 23 * 2^108 := by rw [c3_post]; omega
  -- c4 = a2·a2 + 2·(a0·a4 + a1·a3)
  let* ⟨ i25, i25_post ⟩ ← pow2k_m_spec by dis
  have hv_i25 : i25.val < 2^108 := by
    rw [i25_post]; have := Nat.mul_lt_mul'' hv_i6 hv_i6; omega
  let* ⟨ i26, i26_post ⟩ ← pow2k_m_spec by dis
  have hv_i26 : i26.val < 2^108 := by
    rw [i26_post]; have := Nat.mul_lt_mul'' hv_i2 hv_i1; omega
  let* ⟨ i27, i27_post ⟩ ← pow2k_m_spec by dis
  have hv_i27 : i27.val < 2^108 := by
    rw [i27_post]; have := Nat.mul_lt_mul'' hv_i4 hv_i; omega
  let* ⟨ i28, i28_post ⟩ ← U128.add_spec by scalar_tac
  have hv_i28 : i28.val < 2 * 2^108 := by rw [i28_post]; omega
  let* ⟨ i29, i29_post ⟩ ← U128.mul_spec by scalar_tac
  have hv_i29 : i29.val < 4 * 2^108 := by rw [i29_post]; omega
  let* ⟨ c4, c4_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c4 : c4.val < 5 * 2^108 := by rw [c4_post]; omega
  -- debug_assert limbs < 2^54 (massert)
  let* ⟨ i30, i30_post1, i30_post2 ⟩ ← U64.ShiftLeft_IScalar_spec by dis
  have hv_i30 : i30.val = 2^54 := by
    rw [i30_post1]; simp [Nat.shiftLeft_eq, U64.size, U64.numBits]
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  -- carry c0 -> c11; limb 0
  let* ⟨ i31, i31_post1, i31_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i32, i32_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i33, i33_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i33 : i33.val = c0.val / 2^51 := by
    simp [i33_post, i32_post, i31_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c11, c11_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c11 : c11.val < 60 * 2^108 := by
    rw [c11_post]; omega
  let* ⟨ i34, i34_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i35, i35_post ⟩ ← pow2k_mask_spec by dis
  let* ⟨ i36, i36_post1, i36_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i36 : i36.val = c0.val % 2^51 := by
    simp [i36_post1, i34_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a1, a1_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c11 -> c21; limb 1
  let* ⟨ i37, i37_post1, i37_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i38, i38_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i39, i39_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i39 : i39.val = c11.val / 2^51 := by
    simp [i39_post, i38_post, i37_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c21, c21_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c21 : c21.val < 42 * 2^108 := by
    rw [c21_post]; omega
  let* ⟨ i40, i40_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i41, i41_post1, i41_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i41 : i41.val = c11.val % 2^51 := by
    simp [i41_post1, i40_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a2, a2_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c21 -> c31; limb 2
  let* ⟨ i42, i42_post1, i42_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i43, i43_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i44, i44_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i44 : i44.val = c21.val / 2^51 := by
    simp [i44_post, i43_post, i42_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c31, c31_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c31 : c31.val < 24 * 2^108 := by
    rw [c31_post]; omega
  let* ⟨ i45, i45_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i46, i46_post1, i46_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i46 : i46.val = c21.val % 2^51 := by
    simp [i46_post1, i45_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a3, a3_post ⟩ ← Array.update_spec by scalar_tac
  -- carry c31 -> c41; limb 3
  let* ⟨ i47, i47_post1, i47_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ i48, i48_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i49, i49_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_i49 : i49.val = c31.val / 2^51 := by
    simp [i49_post, i48_post, i47_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ c41, c41_post ⟩ ← U128.add_spec by scalar_tac
  have hv_c41 : c41.val < 6 * 2^108 := by
    rw [c41_post]; omega
  let* ⟨ i50, i50_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i51, i51_post1, i51_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i51 : i51.val = c31.val % 2^51 := by
    simp [i51_post1, i50_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a4, a4_post ⟩ ← Array.update_spec by scalar_tac
  -- last limb: carry out of c41
  let* ⟨ i52, i52_post1, i52_post2 ⟩ ← U128.ShiftRight_IScalar_spec by dis
  let* ⟨ carry, carry_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  have hv_carry : carry.val = c41.val / 2^51 := by
    simp [carry_post, i52_post1, UScalar.cast_val_eq, U64.size, U128.size]; omega
  let* ⟨ i53, i53_post ⟩ ← UScalar.cast.step_spec by scalar_tac
  let* ⟨ i54, i54_post1, i54_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i54 : i54.val = c41.val % 2^51 := by
    simp [i54_post1, i53_post, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ a5, a5_post ⟩ ← Array.update_spec by scalar_tac
  -- fold the final carry * 19 into limb 0, then the mini-carry into limb 1
  let* ⟨ i55, i55_post ⟩ ← U64.mul_spec by scalar_tac
  let* ⟨ i56, i56_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i56 : i56.val = c0.val % 2^51 := by
    simp [i56_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, hv_i36]
  let* ⟨ i57, i57_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ a6, a6_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i58, i58_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i58 : i58.val = i57.val := by
    simp [i58_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq]
  let* ⟨ i59, i59_post1, i59_post2 ⟩ ← U64.ShiftRight_IScalar_spec by scalar_tac
  let* ⟨ i60, i60_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i60 : i60.val = c11.val % 2^51 := by
    simp [i60_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, hv_i41]
  let* ⟨ i61, i61_post ⟩ ← U64.add_spec by scalar_tac
  let* ⟨ a7, a7_post ⟩ ← Array.update_spec by scalar_tac
  let* ⟨ i62, i62_post ⟩ ← Array.index_usize_spec by scalar_tac
  have hv_i62 : i62.val = i57.val := by
    simp [i62_post, a7_post, a6_post, a5_post, a4_post, a3_post, a2_post,
          a1_post, Array.set_val_eq]
  let* ⟨ i63, i63_post1, i63_post2 ⟩ ← UScalar.and_spec by scalar_tac
  have hv_i63 : i63.val = i57.val % 2^51 := by
    simp [i63_post1, hv_i62, i35_post, UScalar.cast_val_eq, U64.size, U128.size]
  let* ⟨ q, back, q_post, back_post ⟩ ← Array.index_mut_usize_spec by scalar_tac
  -- the result limb list (a8 = a7.set 0 i63 in both branches)
  have hv_i59 : i59.val = i57.val / 2^51 := by
    simp [i59_post1, hv_i58]
  have hout : (↑(a7.set 0#usize i63) : List U64) = [i63, i61, i46, i51, i54] := by
    simp [a7_post, a6_post, a5_post, a4_post, a3_post, a2_post, a1_post,
          Array.set_val_eq, ha]
  have hbnd8 : Bnd (a7.set 0#usize i63) (2^51 + 2^13) :=
    (Bnd_eq _ _ _ _ _ _ _ hout).mpr
      ⟨by omega, by omega, by omega, by omega, by omega⟩
  -- exact ℕ accounting of the carry pass
  have hkey : feVal (a7.set 0#usize i63) + P * carry.val
      = c0.val + 2^51*c1.val + 2^102*c2.val + 2^153*c3.val + 2^204*c4.val := by
    rw [feVal_eq _ _ _ _ _ _ hout]; simp only [limbsVal, P]; omega
  -- ℕ product expansions of the five columns
  have hnc0 : c0.val = x0.val*x0.val + 38*(x1.val*x4.val) + 38*(x2.val*x3.val) := by
    simp only [c0_post, i9_post, i8_post, i3_post, i5_post, i7_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc1 : c1.val = 2*(x0.val*x1.val) + 19*(x3.val*x3.val) + 38*(x2.val*x4.val) := by
    simp only [c1_post, i14_post, i13_post, i10_post, i11_post, i12_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc2 : c2.val = x1.val*x1.val + 2*(x0.val*x2.val) + 38*(x3.val*x4.val) := by
    simp only [c2_post, i19_post, i18_post, i15_post, i16_post, i17_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc3 : c3.val = 19*(x4.val*x4.val) + 2*(x0.val*x3.val) + 2*(x1.val*x2.val) := by
    simp only [c3_post, i24_post, i23_post, i20_post, i21_post, i22_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  have hnc4 : c4.val = x2.val*x2.val + 2*(x0.val*x4.val) + 2*(x1.val*x3.val) := by
    simp only [c4_post, i29_post, i28_post, i25_post, i26_post, i27_post,
              a3_19_post, a4_19_post, he_i, he_i1, he_i2, he_i4, he_i6]
    ring
  -- 𝔽_p bridge: A·A = Σ cᵢ·2⁵¹ⁱ using 2²⁵⁵ = 19
  have h255 : (2:Fp)^255 = 19 := by
    have h := two_pow_255_eq; push_cast at h; simpa using h
  have hAA : ((feVal a : ℕ) : Fp) * ((feVal a : ℕ) : Fp)
      = ((c0.val : ℕ) : Fp) + 2^51*(c1.val : ℕ) + 2^102*(c2.val : ℕ)
        + 2^153*(c3.val : ℕ) + 2^204*(c4.val : ℕ) := by
    rw [feVal_eq a x0 x1 x2 x3 x4 ha]
    simp only [limbsVal, hnc0, hnc1, hnc2, hnc3, hnc4]
    push_cast
    linear_combination (2*(x1.val:Fp)*(x4.val:Fp) + 2*(x2.val:Fp)*(x3.val:Fp)
      + 2^51*(2*(x2.val:Fp)*(x4.val:Fp) + (x3.val:Fp)*(x3.val:Fp))
      + 2^102*(2*(x3.val:Fp)*(x4.val:Fp))
      + 2^153*((x4.val:Fp)*(x4.val:Fp))) * h255
  -- conclude the denotation fact
  have hc := congrArg (Nat.cast : ℕ → Fp) hkey
  push_cast at hc
  have hp0 : ((P : ℕ) : Fp) = 0 := ZMod.natCast_self P
  rw [hp0] at hc
  simp only [zero_mul, add_zero] at hc
  have hfin : ⟪a7.set 0#usize i63⟫ = ⟪a⟫ * ⟪a⟫ := by
    simp only [denote]
    linear_combination hc - hAA
  -- k decrement + branch on k1 = 0
  let* ⟨ k1, k1_post1, k1_post2 ⟩ ← U32.sub_spec by scalar_tac
  split
  next hcond =>
    have hkv : k.val = 1 := by
      have h0 : k1.val = 0 := by rw [hcond]; scalar_tac
      scalar_tac
    simp only [spec_ok]
    exact Or.inl ⟨hkv, a7.set 0#usize i63, by rw [back_post], hbnd8, hfin⟩
  next hcond =>
    have hkv : 2 ≤ k.val := by
      have h0 : k1.val ≠ 0 := fun hh => hcond (UScalar.eq_of_val_eq (by scalar_tac))
      scalar_tac
    simp only [spec_ok]
    exact Or.inr ⟨hkv, k1, a7.set 0#usize i63, by rw [back_post],
      by scalar_tac, hbnd8, hfin⟩

/-- Fuel-indexed loop spec: `pow2k_loop k a` computes `⟪a⟫ ^ (2^k)`. -/
theorem pow2k_loop_spec_aux (n : ℕ) (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) (hkn : k.val ≤ n) :
    backend.serial.u64.field.FieldElement51.pow2k_loop k a
      ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  induction n generalizing k a x0 x1 x2 x3 x4 with
  | zero => exact absurd hkn (by omega)
  | succ n ih =>
    unfold backend.serial.u64.field.FieldElement51.pow2k_loop
    apply loop_step
    apply spec_mono (pow2k_body_spec k a x0 x1 x2 x3 x4 ha hba hk)
    rintro cf (⟨hk1, r, rfl, hbr, hr⟩ | ⟨hk2, k1, r, rfl, hk1v, hbr, hr⟩)
    · -- done: k = 1, one squaring
      refine ⟨hbr, ?_⟩
      rw [hr, hk1]
      ring
    · -- cont: recurse on (k-1, a²)
      obtain ⟨r0, r1, r2, r3, r4, hrl⟩ := Fe.exists_limbs r
      have hih := ih k1 r r0 r1 r2 r3 r4 hrl (hbr.mono (by norm_num))
        (by omega) (by omega)
      unfold backend.serial.u64.field.FieldElement51.pow2k_loop at hih
      apply spec_mono hih
      rintro r' ⟨hbr', hr'⟩
      refine ⟨hbr', ?_⟩
      have hexp : 2 * 2 ^ (k.val - 1) = 2 ^ k.val := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hr', hr, hk1v, ← hexp, pow_mul]
      ring

/-- Loop spec: `pow2k_loop k a` computes `⟪a⟫ ^ (2^k)` (limbs < 2⁵¹ + 2¹³). -/
theorem pow2k_loop_spec (k : U32) (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    backend.serial.u64.field.FieldElement51.pow2k_loop k a
      ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ :=
  pow2k_loop_spec_aux k.val k a x0 x1 x2 x3 x4 ha hba hk (Nat.le_refl _)

/-- Main spec for `pow2k`: under the 2⁵⁴ invariant and `k ≥ 1`, no panic,
    output limbs < 2⁵¹ + 2¹³, and the denotation is `⟪a⟫ ^ (2^k)`. -/
@[step]
theorem pow2k_spec (a : Fe) (k : U32) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    fe_pow2k a k ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  unfold fe_pow2k backend.serial.u64.field.FieldElement51.pow2k
  let* ⟨ _ ⟩ ← massert_spec by scalar_tac
  first
  | exact pow2k_loop_spec k a x0 x1 x2 x3 x4 ha hba hk
  | (apply spec_bind (pow2k_loop_spec k a x0 x1 x2 x3 x4 ha hba hk);
     intro r hr;
     simp only [spec_ok];
     exact hr)

/-- Main spec for `square`: under the 2⁵⁴ invariant, no panic, output limbs
    < 2⁵¹ + 2¹³, and the denotation squares in 𝔽_p. -/
@[step]
theorem square_spec (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) :
    fe_square a ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫ ⦄ := by
  unfold fe_square backend.serial.u64.field.FieldElement51.square
  apply spec_mono (pow2k_spec a 1#u32 x0 x1 x2 x3 x4 ha hba (by scalar_tac))
  rintro r ⟨hbr, hr⟩
  refine ⟨hbr, ?_⟩
  have h1 : (1#u32).val = 1 := by scalar_tac
  rw [hr, h1]
  ring

end CurveFieldProofs
