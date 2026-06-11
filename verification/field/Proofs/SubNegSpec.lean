/- Specs for the transpiled `sub` (a + 16p − b, then reduce) and `negate`
   (16p − a, then reduce): no panic under the 2⁵⁴ invariant, output < 2⁵²,
   and the denotation is subtraction/negation in 𝔽_p. -/
import Proofs.ReduceSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-- `reduce` applied to a literal `Array.make` — composition-friendly form. -/
@[step]
theorem reduce_make_spec (x0 x1 x2 x3 x4 : U64) :
    fe_reduce (Array.make 5#usize [x0, x1, x2, x3, x4]) ⦃ r =>
      Bnd r (2^51 + 19 * 2^13) ∧
      feVal r + P * (x4.val / 2^51) = limbsVal x0 x1 x2 x3 x4 ⦄ := by
  have h : (↑(Array.make 5#usize [x0, x1, x2, x3, x4]) : List U64)
      = [x0, x1, x2, x3, x4] := rfl
  have hs := reduce_spec (Array.make 5#usize [x0, x1, x2, x3, x4])
    x0 x1 x2 x3 x4 h
  simpa [feVal_eq _ _ _ _ _ _ h] using hs

/-- Σ Cᵢ·2⁵¹ⁱ for the sub/neg constants (C₀ = 16(2⁵¹−19), Cᵢ = 16(2⁵¹−1))
    is exactly 16p. -/
theorem sixteen_p :
    36028797018963664 + 2^51 * 36028797018963952 + 2^102 * 36028797018963952
      + 2^153 * 36028797018963952 + 2^204 * 36028797018963952 = 16 * P := by
  norm_num [P]

/-- The casting bridge: from the exact ℕ-level equation to 𝔽_p. -/
theorem cast_key {x y k m : ℕ} (h : x + P * k + y = m + 16 * P) :
    (x : Fp) = (m : Fp) - (y : Fp) := by
  have hc := congrArg (Nat.cast : ℕ → Fp) h
  push_cast at hc
  rw [eq_sub_iff_add_eq]
  simpa using hc

theorem sub_spec (a b : Fe) (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hb : (↑b : List U64) = [y0, y1, y2, y3, y4])
    (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_sub a b ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ ⦄ := by
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  rw [Bnd_eq b y0 y1 y2 y3 y4 _ hb] at hbb
  unfold fe_sub
    Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51.sub
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i1, i1_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i5, i5_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i9, i9_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i10, i10_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i11, i11_post1, i11_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i12, i12_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i13, i13_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i14, i14_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i15, i15_post1, i15_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i16, i16_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i17, i17_post ⟩ ← U64.add_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i18, i18_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i19, i19_post1, i19_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ r, r_post1, r_post2 ⟩ ← reduce_make_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  refine ⟨r_post1.mono (by norm_num), ?_⟩
  -- Exact ℕ-level accounting: result + P·carry + b = a + 16p.
  have key : feVal r + P * (i19.val / 2^51) + feVal b
      = feVal a + 16 * P := by
    rw [r_post2, feVal_eq a x0 x1 x2 x3 x4 ha, feVal_eq b y0 y1 y2 y3 y4 hb]
    simp only [limbsVal] at *
    -- All limb equations (incl. ℕ-subtractions with their ≤ side facts) are
    -- in context; 16p is the constant sum (sixteen_p). Linear: omega.
    have h16 := sixteen_p
    simp [i_post, i2_post, i4_post, i6_post, i8_post, i10_post, i12_post,
          i14_post, i16_post, i18_post, ha, hb] at *
    omega
  simpa [denote] using cast_key key

theorem neg_spec (a : Fe) (x0 x1 x2 x3 x4 : U64)
    (ha : (↑a : List U64) = [x0, x1, x2, x3, x4])
    (hba : Bnd a (2^54)) :
    fe_neg a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ ⦄ := by
  rw [Bnd_eq a x0 x1 x2 x3 x4 _ ha] at hba
  unfold fe_neg backend.serial.u64.field.FieldElement51.negate
  let* ⟨ i, i_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i1, i1_post1, i1_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i2, i2_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i3, i3_post1, i3_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i4, i4_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i5, i5_post1, i5_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i6, i6_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i7, i7_post1, i7_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i8, i8_post ⟩ ← Array.index_usize_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ i9, i9_post1, i9_post2 ⟩ ← U64.sub_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  let* ⟨ neg, neg_post1, neg_post2 ⟩ ← reduce_make_spec
    by(subst_vars; try simp [Array.set_val_eq, *]; try scalar_tac)
  refine ⟨neg_post1.mono (by norm_num), ?_⟩
  have key : feVal neg + P * (i9.val / 2^51) + feVal a
      = 0 + 16 * P := by
    rw [neg_post2, feVal_eq a x0 x1 x2 x3 x4 ha]
    simp only [limbsVal] at *
    have h16 := sixteen_p
    simp [i_post, i2_post, i4_post, i6_post, i8_post, ha] at *
    omega
  have := cast_key key
  simpa [denote] using this

end CurveFieldProofs
