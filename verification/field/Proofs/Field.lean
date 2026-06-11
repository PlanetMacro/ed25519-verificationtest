/- Field packaging (part 1 — everything except multiplicative inverses, which
   land in InvertSpec.lean / FieldMain.lean):

   * 𝔽_p IS a field: p = 2²⁵⁵ − 19 is prime (Proofs/P25519.lean, axiom-free),
     so mathlib's `ZMod.instField` applies.
   * The denotation ⟪·⟫ : Fe → 𝔽_p is SURJECTIVE on bounded elements (via the
     canonical `encode`), so the transpiled type covers all of 𝔽_p.
   * The transpiled ops realize the field ops of 𝔽_p through ⟪·⟫. -/
import Proofs.ConstSpecs
import Proofs.AddSpec
import Proofs.SubNegSpec
import Proofs.MulSpec
import Proofs.P25519
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000

namespace CurveFieldProofs

/-! ## 𝔽_p is a field -/

theorem P_prime : Nat.Prime P := by
  have h := p25519_prime
  have : (2:ℕ)^255 - 19 = P := by norm_num [P]
  rwa [this] at h

instance : Fact (Nat.Prime P) := ⟨P_prime⟩

instance : NeZero P := ⟨by norm_num [P]⟩

/-- 𝔽_p = ZMod p with p prime is a field (mathlib instance). -/
noncomputable example : Field Fp := inferInstance

/-! ## Surjectivity of the denotation -/

/-- Build a `U64` from a natural number (mod 2⁶⁴). -/
def mkU64 (n : ℕ) : U64 := ⟨BitVec.ofNat 64 n⟩

theorem mkU64_val (n : ℕ) (h : n < 2^64) : (mkU64 n).val = n := by
  show (BitVec.ofNat 64 n).toNat = n
  simp only [BitVec.toNat_ofNat]
  omega

/-- Canonical (reduced, base-2⁵¹) representative of a field element. -/
def encode (y : Fp) : Fe :=
  Array.make 5#usize
    [ mkU64 (y.val % 2^51),
      mkU64 (y.val / 2^51 % 2^51),
      mkU64 (y.val / 2^102 % 2^51),
      mkU64 (y.val / 2^153 % 2^51),
      mkU64 (y.val / 2^204) ]

theorem encode_list (y : Fp) :
    (↑(encode y) : List U64)
      = [ mkU64 (y.val % 2^51), mkU64 (y.val / 2^51 % 2^51),
          mkU64 (y.val / 2^102 % 2^51), mkU64 (y.val / 2^153 % 2^51),
          mkU64 (y.val / 2^204) ] := rfl

theorem val_lt_P (y : Fp) : y.val < P := ZMod.val_lt y

theorem encode_bnd (y : Fp) : Bnd (encode y) (2^51) := by
  have h := val_lt_P y
  have hP : P < 2^255 := by norm_num [P]
  rw [Bnd_eq _ _ _ _ _ _ _ (encode_list y)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [mkU64_val _ (by omega)]; omega)

theorem denote_encode (y : Fp) : ⟪encode y⟫ = y := by
  have h := val_lt_P y
  have hP : P < 2^255 := by norm_num [P]
  have hval : feVal (encode y) = y.val := by
    rw [feVal_eq _ _ _ _ _ _ (encode_list y)]
    simp only [limbsVal]
    rw [mkU64_val _ (by omega), mkU64_val _ (by omega), mkU64_val _ (by omega),
        mkU64_val _ (by omega), mkU64_val _ (by omega)]
    omega
  simp [denote, hval, ZMod.natCast_val, ZMod.cast_id]

/-- Every element of 𝔽_p is the denotation of a (well-bounded) `Fe`. -/
theorem denote_surjective : ∀ y : Fp, ∃ a : Fe, Bnd a (2^52) ∧ ⟪a⟫ = y :=
  fun y => ⟨encode y, (encode_bnd y).mono (by norm_num), denote_encode y⟩

/-! ## The triple → existential bridge (library: `Std.WP.spec_imp_exists`) -/

theorem spec_exists {α} {x : Result α} {p : α → Prop}
    (h : x ⦃ r => p r ⦄) : ∃ r, x = ok r ∧ p r :=
  Std.WP.spec_imp_exists h

end CurveFieldProofs
