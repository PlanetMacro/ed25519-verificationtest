/-
`Nat.Prime (2 ^ 255 - 19)` — the Curve25519 base field prime — via Lucas/Pratt
certificates (`lucas_primality` from mathlib). Axiom-free, no `native_decide`;
all modular arithmetic is discharged by kernel `decide` through a fuel-based
binary modular-exponentiation function.
-/
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime

set_option maxRecDepth 8000

namespace P25519

/-- Fuel-based binary modular exponentiation, kernel-reducible (GMP-fast `decide`). -/
def powModAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, n => 1 % n
  | fuel + 1, a, k, n =>
    if k = 0 then 1 % n
    else if k % 2 = 1 then powModAux fuel (a * a % n) (k / 2) n * a % n
    else powModAux fuel (a * a % n) (k / 2) n

theorem powModAux_eq : ∀ (fuel a k n : ℕ), k < 2 ^ fuel → powModAux fuel a k n = a ^ k % n := by
  intro fuel
  induction fuel with
  | zero =>
    intro a k n hk
    rw [pow_zero] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    simp [powModAux]
  | succ f ih =>
    intro a k n hk
    by_cases hk0 : k = 0
    · subst hk0; simp [powModAux]
    · have hk2 : k / 2 < 2 ^ f := by
        rw [pow_succ] at hk
        omega
      have hrec := ih (a * a % n) (k / 2) n hk2
      have haa : a * a = a ^ 2 := (pow_two a).symm
      simp only [powModAux, if_neg hk0]
      by_cases hodd : k % 2 = 1
      · rw [if_pos hodd, hrec, ← Nat.pow_mod, Nat.mod_mul_mod, haa, ← pow_mul, ← pow_succ,
          show 2 * (k / 2) + 1 = k by omega]
      · rw [if_neg hodd, hrec, ← Nat.pow_mod, haa, ← pow_mul,
          show 2 * (k / 2) = k by omega]

/-- `powMod a k n = a ^ k % n` for all `k < 2 ^ 256`. -/
def powMod (a k n : ℕ) : ℕ := powModAux 256 a k n

theorem cast_pow_eq (a k n : ℕ) (hk : k < 2 ^ 256) :
    (a : ZMod n) ^ k = ((powMod a k n : ℕ) : ZMod n) := by
  rw [powMod, powModAux_eq 256 a k n hk, ZMod.natCast_mod, Nat.cast_pow]

theorem pow_eq_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (h : powMod a k n = 1) :
    (a : ZMod n) ^ k = 1 := by
  rw [cast_pow_eq a k n hk, h, Nat.cast_one]

theorem pow_ne_one_of_powMod (a k n : ℕ) (hk : k < 2 ^ 256) (hn : 1 < n)
    (h1 : powMod a k n ≠ 1) (h2 : powMod a k n < n) :
    (a : ZMod n) ^ k ≠ 1 := by
  rw [cast_pow_eq a k n hk]
  intro hcon
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) by rw [Nat.cast_one],
      ZMod.natCast_eq_natCast_iff'] at hcon
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt hn] at hcon
  exact h1 hcon

theorem prime_8574133 : Nat.Prime 8574133 := by
  refine lucas_primality 8574133 ((2 : ℕ) : ZMod 8574133) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (8574133 - 1) 8574133 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (8574133 : ℕ) - 1 = 2 ^ 2 * (3 * (7 * (103 * (991)))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 2) 8574133 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 3) 8574133 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 7) 8574133 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 103 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 103) 8574133 (by decide) (by decide) (by decide) (by decide)
    have he : q = 991 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((8574133 - 1) / 991) 8574133 (by decide) (by decide) (by decide) (by decide)

theorem prime_2773320623 : Nat.Prime 2773320623 := by
  refine lucas_primality 2773320623 ((5 : ℕ) : ZMod 2773320623) ?_ ?_
  · exact pow_eq_one_of_powMod 5 (2773320623 - 1) 2773320623 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (2773320623 : ℕ) - 1 = 2 * (2437 * (569003)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 2) 2773320623 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2437 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 2437) 2773320623 (by decide) (by decide) (by decide) (by decide)
    have he : q = 569003 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 5 ((2773320623 - 1) / 569003) 2773320623 (by decide) (by decide) (by decide) (by decide)

theorem prime_72106336199 : Nat.Prime 72106336199 := by
  refine lucas_primality 72106336199 ((7 : ℕ) : ZMod 72106336199) ?_ ?_
  · exact pow_eq_one_of_powMod 7 (72106336199 - 1) 72106336199 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (72106336199 : ℕ) - 1 = 2 * (13 * (2773320623)) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 2) 72106336199 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 13) 72106336199 (by decide) (by decide) (by decide) (by decide)
    have he : q = 2773320623 := (Nat.prime_dvd_prime_iff_eq hq prime_2773320623).mp hqd
    subst he
    exact pow_ne_one_of_powMod 7 ((72106336199 - 1) / 2773320623) 72106336199 (by decide) (by decide) (by decide) (by decide)

theorem prime_1919519569386763 : Nat.Prime 1919519569386763 := by
  refine lucas_primality 1919519569386763 ((2 : ℕ) : ZMod 1919519569386763) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (1919519569386763 - 1) 1919519569386763 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (1919519569386763 : ℕ) - 1 = 2 * (3 * (7 * (19 * (47 ^ 2 * (127 * (8574133)))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 2) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 3) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 7 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 7) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 19 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 19) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 47 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 47) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 127) 1919519569386763 (by decide) (by decide) (by decide) (by decide)
    have he : q = 8574133 := (Nat.prime_dvd_prime_iff_eq hq prime_8574133).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((1919519569386763 - 1) / 8574133) 1919519569386763 (by decide) (by decide) (by decide) (by decide)

theorem prime_31757755568855353 : Nat.Prime 31757755568855353 := by
  refine lucas_primality 31757755568855353 ((10 : ℕ) : ZMod 31757755568855353) ?_ ?_
  · exact pow_eq_one_of_powMod 10 (31757755568855353 - 1) 31757755568855353 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (31757755568855353 : ℕ) - 1 = 2 ^ 3 * (3 * (31 * (107 * (223 * (4153 * (430751)))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 2) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 3) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 31 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 31) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 107 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 107) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 223 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 223) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 4153 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 4153) 31757755568855353 (by decide) (by decide) (by decide) (by decide)
    have he : q = 430751 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hqd
    subst he
    exact pow_ne_one_of_powMod 10 ((31757755568855353 - 1) / 430751) 31757755568855353 (by decide) (by decide) (by decide) (by decide)

theorem prime_75445702479781427272750846543864801 : Nat.Prime 75445702479781427272750846543864801 := by
  refine lucas_primality 75445702479781427272750846543864801 ((7 : ℕ) : ZMod 75445702479781427272750846543864801) ?_ ?_
  · exact pow_eq_one_of_powMod 7 (75445702479781427272750846543864801 - 1) 75445702479781427272750846543864801 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (75445702479781427272750846543864801 : ℕ) - 1 = 2 ^ 5 * (3 ^ 2 * (5 ^ 2 * (75707 * (72106336199 * (1919519569386763))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 2) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 3) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 5) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 75707 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 75707) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 72106336199 := (Nat.prime_dvd_prime_iff_eq hq prime_72106336199).mp h
      subst he
      exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 72106336199) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)
    have he : q = 1919519569386763 := (Nat.prime_dvd_prime_iff_eq hq prime_1919519569386763).mp hqd
    subst he
    exact pow_ne_one_of_powMod 7 ((75445702479781427272750846543864801 - 1) / 1919519569386763) 75445702479781427272750846543864801 (by decide) (by decide) (by decide) (by decide)

theorem prime_74058212732561358302231226437062788676166966415465897661863160754340907 : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 := by
  refine lucas_primality 74058212732561358302231226437062788676166966415465897661863160754340907 ((2 : ℕ) : ZMod 74058212732561358302231226437062788676166966415465897661863160754340907) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (74058212732561358302231226437062788676166966415465897661863160754340907 - 1) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (74058212732561358302231226437062788676166966415465897661863160754340907 : ℕ) - 1 = 2 * (3 * (353 * (57467 * (132049 * (1923133 * (31757755568855353 * (75445702479781427272750846543864801))))))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 2) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 3) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 353 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 353) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 57467 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 57467) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 132049 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 132049) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 1923133 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 1923133) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 31757755568855353 := (Nat.prime_dvd_prime_iff_eq hq prime_31757755568855353).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 31757755568855353) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)
    have he : q = 75445702479781427272750846543864801 := (Nat.prime_dvd_prime_iff_eq hq prime_75445702479781427272750846543864801).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((74058212732561358302231226437062788676166966415465897661863160754340907 - 1) / 75445702479781427272750846543864801) 74058212732561358302231226437062788676166966415465897661863160754340907 (by decide) (by decide) (by decide) (by decide)

theorem prime_57896044618658097711785492504343953926634992332820282019728792003956564819949 : Nat.Prime 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by
  refine lucas_primality 57896044618658097711785492504343953926634992332820282019728792003956564819949 ((2 : ℕ) : ZMod 57896044618658097711785492504343953926634992332820282019728792003956564819949) ?_ ?_
  · exact pow_eq_one_of_powMod 2 (57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide)
  · intro q hq hqd
    have hfac : (57896044618658097711785492504343953926634992332820282019728792003956564819949 : ℕ) - 1 = 2 ^ 2 * (3 * (65147 * (74058212732561358302231226437062788676166966415465897661863160754340907))) := by decide
    rw [hfac] at hqd
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow h)
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 2) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 3) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    rcases (Nat.Prime.dvd_mul hq).mp hqd with h | hqd
    · have he : q = 65147 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
      subst he
      exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 65147) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)
    have he : q = 74058212732561358302231226437062788676166966415465897661863160754340907 := (Nat.prime_dvd_prime_iff_eq hq prime_74058212732561358302231226437062788676166966415465897661863160754340907).mp hqd
    subst he
    exact pow_ne_one_of_powMod 2 ((57896044618658097711785492504343953926634992332820282019728792003956564819949 - 1) / 74058212732561358302231226437062788676166966415465897661863160754340907) 57896044618658097711785492504343953926634992332820282019728792003956564819949 (by decide) (by decide) (by decide) (by decide)

end P25519

/-- The Curve25519 field prime `2 ^ 255 - 19` is prime. -/
theorem p25519_prime : Nat.Prime (2 ^ 255 - 19) := by
  have h : (2 : ℕ) ^ 255 - 19 = 57896044618658097711785492504343953926634992332820282019728792003956564819949 := by decide
  rw [h]
  exact P25519.prime_57896044618658097711785492504343953926634992332820282019728792003956564819949
