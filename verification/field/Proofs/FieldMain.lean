/- MAIN RESULT: the transpiled `FieldElement51` code implements the field
   𝔽_p, p = 2²⁵⁵ − 19.

   Because the representation is redundant (a field element has many limb
   representations) and the operations are partial (machine arithmetic can
   overflow → the `Result` monad), "the transpiled code is a field" is
   formalized the standard way for such implementations:

     * 𝔽_p (= `ZMod P`) IS a field          — mathlib instance + our
       axiom-free primality certificate for p (Proofs/P25519.lean);
     * the denotation ⟪·⟫ : Fe → 𝔽_p is surjective on bounded elements;
     * every transpiled operation TOTALLY (no panic) realizes the
       corresponding field operation of 𝔽_p through ⟪·⟫, under the
       documented limb-bound invariant (the dalek 2⁵⁴ discipline, which the
       Rust code itself asserts via debug_assert! → `massert`);
     * consequently every field axiom holds for the implementation up to
       denotation — proved below as the `impl_*` corollaries.

   Nothing in gen/ (the transpiled code) was modified. -/
import Proofs.InvertSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000

namespace CurveFieldProofs

/-! ## Runners: totality + facts for each transpiled op -/

theorem run_zero : ∃ z, fe_zero = ok z ∧ Bnd z (2^52) ∧ ⟪z⟫ = 0 := by
  obtain ⟨z, hz, _, h1, h2⟩ := spec_exists zero_spec
  exact ⟨z, hz, h1.mono (by norm_num), h2⟩

theorem run_one : ∃ o, fe_one = ok o ∧ Bnd o (2^52) ∧ ⟪o⟫ = 1 := by
  obtain ⟨o, ho, h1, h2⟩ := spec_exists one_spec
  exact ⟨o, ho, h1.mono (by norm_num), h2⟩

theorem run_add {a b : Fe} (ha : Bnd a (2^52)) (hb : Bnd b (2^52)) :
    ∃ r, fe_add a b = ok r ∧ Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫ := by
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs b
  have hba := (Bnd_eq a _ _ _ _ _ _ hla).mp ha
  have hbb := (Bnd_eq b _ _ _ _ _ _ hlb).mp hb
  obtain ⟨r, hr, _, hval, hbnd⟩ :=
    spec_exists (add_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  refine ⟨r, hr, by simpa using hbnd (2^52) ha hb, ?_⟩
  simp [denote, hval]

theorem run_sub {a b : Fe} (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    ∃ r, fe_sub a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫ := by
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs b
  exact spec_exists (sub_spec a b x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb ha hb)

theorem run_neg {a : Fe} (ha : Bnd a (2^54)) :
    ∃ r, fe_neg a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫ := by
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs a
  exact spec_exists (neg_spec a x0 x1 x2 x3 x4 hla ha)

theorem run_mul {a b : Fe} (ha : Bnd a (2^54)) (hb : Bnd b (2^54)) :
    ∃ r, fe_mul a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫ := by
  obtain ⟨r, hr, h1, h2⟩ := spec_exists (mul_spec' a b ha hb)
  exact ⟨r, hr, h1.mono (by norm_num), h2⟩

theorem run_invert {a : Fe} (ha : Bnd a (2^54)) :
    ∃ r, fe_invert a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹ :=
  spec_exists (invert_spec a ha)

/-! ## The field-implementation certificate -/

/-- The transpiled curve25519 field code implements the field 𝔽_p through the
    denotation ⟪·⟫ on limb-bounded elements: all operations are total (no
    panics / overflows) on the invariant and realize the field structure. -/
structure IsFieldImplementation : Prop where
  /-- 𝔽_p is reachable: every field element has a bounded representative. -/
  surj : ∀ y : Fp, ∃ a : Fe, Bnd a (2^52) ∧ ⟪a⟫ = y
  /-- 0 and 1 are correctly implemented (and distinct: see `zero_ne_one`). -/
  zero_ok : ∃ z, fe_zero = ok z ∧ Bnd z (2^52) ∧ ⟪z⟫ = 0
  one_ok : ∃ o, fe_one = ok o ∧ Bnd o (2^52) ∧ ⟪o⟫ = 1
  /-- addition (limbwise, unreduced — hence the 2⁵³ output bound) -/
  add_ok : ∀ a b, Bnd a (2^52) → Bnd b (2^52) →
    ∃ r, fe_add a b = ok r ∧ Bnd r (2^53) ∧ ⟪r⟫ = ⟪a⟫ + ⟪b⟫
  sub_ok : ∀ a b, Bnd a (2^54) → Bnd b (2^54) →
    ∃ r, fe_sub a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ - ⟪b⟫
  neg_ok : ∀ a, Bnd a (2^54) →
    ∃ r, fe_neg a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = -⟪a⟫
  mul_ok : ∀ a b, Bnd a (2^54) → Bnd b (2^54) →
    ∃ r, fe_mul a b = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫ * ⟪b⟫
  /-- multiplicative inverse (x^(p−2); maps 0 to 0, matching 𝔽_p's 0⁻¹ = 0) -/
  inv_ok : ∀ a, Bnd a (2^54) →
    ∃ r, fe_invert a = ok r ∧ Bnd r (2^52) ∧ ⟪r⟫ = ⟪a⟫⁻¹

/-- **The transpiled code implements the field 𝔽_p.** -/
theorem fieldImplementation : IsFieldImplementation where
  surj := denote_surjective
  zero_ok := run_zero
  one_ok := run_one
  add_ok := fun _ _ ha hb => run_add ha hb
  sub_ok := fun _ _ ha hb => run_sub ha hb
  neg_ok := fun _ ha => run_neg ha
  mul_ok := fun _ _ ha hb => run_mul ha hb
  inv_ok := fun _ ha => run_invert ha

/-- 𝔽_p is a field (mathlib instance; p prime by Proofs/P25519.lean). -/
noncomputable abbrev Fp_field : Field Fp := inferInstance

/-! ## The field axioms, at the implementation level

Each `impl_*` theorem runs the actual transpiled operations and states the
corresponding field law up to denotation. They are direct consequences of
the `run_*` specs + the field structure of 𝔽_p. Throughout, `Valid a` means
`Bnd a (2^52)` (the bound every operation re-establishes). -/

abbrev Valid (a : Fe) : Prop := Bnd a (2^52)

theorem valid54 {a : Fe} (h : Valid a) : Bnd a (2^54) := h.mono (by norm_num)

/-- 0 ≠ 1 (the implementation is a nontrivial ring). -/
theorem impl_zero_ne_one :
    ∀ z o, fe_zero = ok z → fe_one = ok o → ⟪z⟫ ≠ ⟪o⟫ := by
  intro z o hz ho
  obtain ⟨z', hz', _, hz0⟩ := run_zero
  obtain ⟨o', ho', _, ho1⟩ := run_one
  rw [hz'] at hz; cases hz
  rw [ho'] at ho; cases ho
  rw [hz0, ho1]
  exact zero_ne_one

/-- Commutativity of implemented addition. -/
theorem impl_add_comm {a b : Fe} (ha : Valid a) (hb : Valid b) :
    ∃ r1 r2, fe_add a b = ok r1 ∧ fe_add b a = ok r2 ∧ ⟪r1⟫ = ⟪r2⟫ := by
  obtain ⟨r1, h1, _, hv1⟩ := run_add ha hb
  obtain ⟨r2, h2, _, hv2⟩ := run_add hb ha
  exact ⟨r1, r2, h1, h2, by rw [hv1, hv2, add_comm]⟩

/-- Associativity of implemented addition ((a+b)+c ≃ a+(b+c)).
    Note 2⁵³+2⁵² < 2⁶⁴: the unreduced intermediate still cannot overflow. -/
theorem impl_add_assoc {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rab rab_c rbc ra_bc,
      fe_add a b = ok rab ∧ fe_add rab c = ok rab_c ∧
      fe_add b c = ok rbc ∧ fe_add a rbc = ok ra_bc ∧
      ⟪rab_c⟫ = ⟪ra_bc⟫ := by
  obtain ⟨rab, h1, hb1, hv1⟩ := run_add ha hb
  obtain ⟨rbc, h3, hb3, hv3⟩ := run_add hb hc
  -- rab : Bnd 2^53, c : 2^52 — rerun the limbwise argument at mixed bounds
  obtain ⟨x0, x1, x2, x3, x4, hla⟩ := Fe.exists_limbs rab
  obtain ⟨y0, y1, y2, y3, y4, hlb⟩ := Fe.exists_limbs c
  have hba := (Bnd_eq rab _ _ _ _ _ _ hla).mp hb1
  have hbb := (Bnd_eq c _ _ _ _ _ _ hlb).mp hc
  obtain ⟨rab_c, h2, _, hval2, _⟩ :=
    spec_exists (add_spec rab c x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 hla hlb
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  obtain ⟨u0, u1, u2, u3, u4, hlu⟩ := Fe.exists_limbs a
  obtain ⟨v0, v1, v2, v3, v4, hlv⟩ := Fe.exists_limbs rbc
  have hbu := (Bnd_eq a _ _ _ _ _ _ hlu).mp ha
  have hbv := (Bnd_eq rbc _ _ _ _ _ _ hlv).mp hb3
  obtain ⟨ra_bc, h4, _, hval4, _⟩ :=
    spec_exists (add_spec a rbc u0 u1 u2 u3 u4 v0 v1 v2 v3 v4 hlu hlv
      ⟨by omega, by omega, by omega, by omega, by omega⟩)
  refine ⟨rab, rab_c, rbc, ra_bc, h1, h2, h3, h4, ?_⟩
  have e2 : ⟪rab_c⟫ = ⟪rab⟫ + ⟪c⟫ := by
    simp [denote, hval2]
  have e4 : ⟪ra_bc⟫ = ⟪a⟫ + ⟪rbc⟫ := by
    simp [denote, hval4]
  rw [e2, e4, hv1, hv3, add_assoc]

/-- 0 + a ≃ a. -/
theorem impl_zero_add {a : Fe} (ha : Valid a) :
    ∃ z r, fe_zero = ok z ∧ fe_add z a = ok r ∧ ⟪r⟫ = ⟪a⟫ := by
  obtain ⟨z, hz, hzb, hz0⟩ := run_zero
  obtain ⟨r, hr, _, hv⟩ := run_add hzb ha
  exact ⟨z, r, hz, hr, by rw [hv, hz0, zero_add]⟩

/-- a + (−a) ≃ 0. -/
theorem impl_add_neg {a : Fe} (ha : Valid a) :
    ∃ n r, fe_neg a = ok n ∧ fe_add a n = ok r ∧ ⟪r⟫ = 0 := by
  obtain ⟨n, hn, hnb, hnv⟩ := run_neg (valid54 ha)
  obtain ⟨r, hr, _, hv⟩ := run_add ha hnb
  exact ⟨n, r, hn, hr, by rw [hv, hnv, add_neg_cancel]⟩

/-- Commutativity of implemented multiplication. -/
theorem impl_mul_comm {a b : Fe} (ha : Valid a) (hb : Valid b) :
    ∃ r1 r2, fe_mul a b = ok r1 ∧ fe_mul b a = ok r2 ∧ ⟪r1⟫ = ⟪r2⟫ := by
  obtain ⟨r1, h1, _, hv1⟩ := run_mul (valid54 ha) (valid54 hb)
  obtain ⟨r2, h2, _, hv2⟩ := run_mul (valid54 hb) (valid54 ha)
  exact ⟨r1, r2, h1, h2, by rw [hv1, hv2, mul_comm]⟩

/-- Associativity of implemented multiplication. -/
theorem impl_mul_assoc {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rab rab_c rbc ra_bc,
      fe_mul a b = ok rab ∧ fe_mul rab c = ok rab_c ∧
      fe_mul b c = ok rbc ∧ fe_mul a rbc = ok ra_bc ∧
      ⟪rab_c⟫ = ⟪ra_bc⟫ := by
  obtain ⟨rab, h1, hb1, hv1⟩ := run_mul (valid54 ha) (valid54 hb)
  obtain ⟨rab_c, h2, _, hv2⟩ := run_mul (valid54 hb1) (valid54 hc)
  obtain ⟨rbc, h3, hb3, hv3⟩ := run_mul (valid54 hb) (valid54 hc)
  obtain ⟨ra_bc, h4, _, hv4⟩ := run_mul (valid54 ha) (valid54 hb3)
  refine ⟨rab, rab_c, rbc, ra_bc, h1, h2, h3, h4, ?_⟩
  rw [hv2, hv4, hv1, hv3, mul_assoc]

/-- 1 * a ≃ a. -/
theorem impl_one_mul {a : Fe} (ha : Valid a) :
    ∃ o r, fe_one = ok o ∧ fe_mul o a = ok r ∧ ⟪r⟫ = ⟪a⟫ := by
  obtain ⟨o, ho, hob, ho1⟩ := run_one
  obtain ⟨r, hr, _, hv⟩ := run_mul (valid54 hob) (valid54 ha)
  exact ⟨o, r, ho, hr, by rw [hv, ho1, one_mul]⟩

/-- a · a⁻¹ ≃ 1 for a ≢ 0 — multiplicative inverses exist. -/
theorem impl_mul_inv_cancel {a : Fe} (ha : Valid a) (h0 : ⟪a⟫ ≠ 0) :
    ∃ i r, fe_invert a = ok i ∧ fe_mul a i = ok r ∧ ⟪r⟫ = 1 := by
  obtain ⟨i, hi, hib, hiv⟩ := run_invert (valid54 ha)
  obtain ⟨r, hr, _, hv⟩ := run_mul (valid54 ha) (valid54 hib)
  exact ⟨i, r, hi, hr, by rw [hv, hiv, mul_inv_cancel₀ h0]⟩

/-- Left distributivity: a·(b+c) ≃ a·b + a·c. -/
theorem impl_left_distrib {a b c : Fe} (ha : Valid a) (hb : Valid b) (hc : Valid c) :
    ∃ rbc r_left rab rac r_right,
      fe_add b c = ok rbc ∧ fe_mul a rbc = ok r_left ∧
      fe_mul a b = ok rab ∧ fe_mul a c = ok rac ∧
      fe_add rab rac = ok r_right ∧
      ⟪r_left⟫ = ⟪r_right⟫ := by
  obtain ⟨rbc, h1, hb1, hv1⟩ := run_add hb hc
  obtain ⟨r_left, h2, _, hv2⟩ := run_mul (valid54 ha) (hb1.mono (by norm_num))
  obtain ⟨rab, h3, hb3, hv3⟩ := run_mul (valid54 ha) (valid54 hb)
  obtain ⟨rac, h4, hb4, hv4⟩ := run_mul (valid54 ha) (valid54 hc)
  obtain ⟨r_right, h5, _, hv5⟩ := run_add hb3 hb4
  refine ⟨rbc, r_left, rab, rac, r_right, h1, h2, h3, h4, h5, ?_⟩
  rw [hv2, hv1, hv5, hv3, hv4, left_distrib]

end CurveFieldProofs
