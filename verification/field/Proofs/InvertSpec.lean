/- Spec for the transpiled `invert`: x ↦ x^(p−2) via the pow22501 addition
   chain, which by Fermat's little theorem (p prime, Proofs/P25519.lean) is
   the multiplicative inverse in 𝔽_p (with the mathlib convention 0⁻¹ = 0,
   which the Rust code also satisfies: invert(0) = 0). -/
import Proofs.MulSpec
import Proofs.SquareSpec
import Proofs.Field
import Mathlib.FieldTheory.Finite.Basic
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## Step-friendly wrappers (no explicit limb lists in the hypotheses) -/

@[step]
theorem mul_spec' (a b : Fe) (hba : Bnd a (2^54)) (hbb : Bnd b (2^54)) :
    fe_mul a b ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hb⟩ := Fe.exists_limbs b
  exact mul_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 ha hb hba hbb

@[step]
theorem square_spec' (a : Fe) (hba : Bnd a (2^54)) :
    fe_square a ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ * ⟪a⟫ ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  exact square_spec a x0 x1 x2 x3 x4 ha hba

@[step]
theorem pow2k_spec' (a : Fe) (k : U32) (hba : Bnd a (2^54)) (hk : 1 ≤ k.val) :
    fe_pow2k a k ⦃ r => Bnd r (2^51 + 2^13) ∧ ⟪r⟫ = ⟪a⟫ ^ (2^k.val) ⦄ := by
  obtain ⟨x0, x1, x2, x3, x4, ha⟩ := Fe.exists_limbs a
  exact pow2k_spec a k x0 x1 x2 x3 x4 ha hba hk

/-- Discharge: linear arithmetic, or a `Bnd` weakening from any hypothesis. -/
macro "bnd" : tactic =>
  `(tactic| (first
      | scalar_tac
      | exact Bnd.mono (by assumption) (by norm_num)))

/-! ## The pow22501 addition chain -/

theorem pow22501_spec (a : Fe) (hba : Bnd a (2^54)) :
    field.FieldElement51.pow22501 a ⦃ rr =>
      Bnd rr.1 (2^52) ∧ Bnd rr.2 (2^52) ∧
      ⟪rr.1⟫ = ⟪a⟫ ^ (2^250 - 1) ∧ ⟪rr.2⟫ = ⟪a⟫ ^ 11 ⦄ := by
  unfold field.FieldElement51.pow22501
  step* by bnd
  refine ⟨by bnd, by bnd, ?_, ?_⟩ <;>
  · simp_all only []
    -- collapse the chain: every post is ⟪·⟫ = (earlier)^e or a product;
    -- rewrite them all, then close by exponent arithmetic.
    simp_all [← pow_mul, ← pow_add, ← pow_succ]
    try ring_nf
    try norm_num

theorem invert_spec (a : Fe) (hba : Bnd a (2^54)) :
    fe_invert a ⦃ r => Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹ ⦄ := by
  unfold fe_invert field.FieldElement51.invert
  let* ⟨ t19, t3, h1, h2, h3, h4 ⟩ ← pow22501_spec by bnd
  let* ⟨ t20, t20_post1, t20_post2 ⟩ ← pow2k_spec' by bnd
  let* ⟨ r, r_post1, r_post2 ⟩ ← mul_spec' by bnd
  refine ⟨by bnd, ?_⟩
  -- ⟪r⟫ = (⟪a⟫^(2^250−1))^(2^5) · ⟪a⟫^11 = ⟪a⟫^(2^255−21) = ⟪a⟫^(P−2) = ⟪a⟫⁻¹
  rw [r_post2, t20_post2, h3, h4]
  rw [← pow_mul, ← pow_add]
  have hexp : (2^250 - 1) * 2^5 + 11 = P - 2 := by
    norm_num [P]
  rw [hexp]
  by_cases h0 : ⟪a⟫ = 0
  · rw [h0]
    rw [zero_pow (by norm_num [P]), inv_zero]
  · -- Fermat: a^(P−1) = 1, hence a · a^(P−2) = 1, hence a^(P−2) = a⁻¹.
    have h1 : ⟪a⟫ ^ (P - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
    have hmul : ⟪a⟫ * ⟪a⟫ ^ (P - 2) = 1 := by
      have hsplit : ⟪a⟫ * ⟪a⟫ ^ (P - 2) = ⟪a⟫ ^ (P - 1) := by
        conv_rhs => rw [show P - 1 = (P - 2) + 1 by norm_num [P]]
        rw [pow_succ]
        ring
      rw [hsplit, h1]
    exact mul_left_cancel₀ h0 (by rw [hmul, mul_inv_cancel₀ h0])

end CurveFieldProofs
