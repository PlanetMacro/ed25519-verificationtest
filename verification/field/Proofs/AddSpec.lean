/- Spec for the transpiled `FieldElement51` addition
   (`impl Add<&FieldElement51> for &FieldElement51`, which calls `AddAssign`):
   it never panics provided the limbwise sums do not overflow u64, and the
   output is the *limbwise* sum — this addition performs NO modular reduction. -/
import Proofs.Denote
import Proofs.ReduceSpec
open Aeneas Aeneas.Std Result
open curve25519

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace CurveFieldProofs

open Aeneas.Std.WP

/-- Unfold one iteration of `Aeneas.Std.loop` under a `spec` goal. -/
theorem loop_step {α : Type u} {β : Type v}
    {body : α → Result (ControlFlow α β)} {x : α} {post : β → Prop}
    (h : body x ⦃ r => match r with
        | .cont x' => Aeneas.Std.loop body x' ⦃ post ⦄
        | .done y => post y ⦄) :
    Aeneas.Std.loop body x ⦃ post ⦄ := by
  obtain ⟨r, hr, hpost⟩ := spec_imp_exists h
  rw [Aeneas.Std.loop.eq_def, hr]
  cases r <;> simpa using hpost

/-- `Iterator::next` on a `usize` range that has not finished yet. -/
theorem range_next_lt_spec (r : core.ops.range.Range Usize)
    (h : r.start.val < r.«end».val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = some r.start ∧ r'.start.val = r.start.val + 1 ∧
                   r'.«end» = r.«end» ⦄ := by
  have hmax : r.start.val + 1 ≤ Usize.max := by scalar_tac
  have hca := Usize.checked_add_bv_spec r.start 1#usize
  unfold core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  simp only [h, decide_true, if_true]
  cases hadd : Usize.checked_add r.start 1#usize with
  | none => rw [hadd] at hca; simp at hca; scalar_tac
  | some n =>
    rw [hadd] at hca
    simp at hca
    simp [spec_ok, hca]

/-- `Iterator::next` on a `usize` range that is finished. -/
theorem range_next_ge_spec (r : core.ops.range.Range Usize)
    (h : r.«end».val ≤ r.start.val) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r
      ⦃ (o, r') => o = none ∧ r' = r ⦄ := by
  unfold core.iter.range.IteratorRange.next
  simp only [core.cmp.impls.PartialOrdUsize.lt,
    core.clone.impls.CloneUsize.clone, core.iter.range.StepUsize.forward_checked,
    liftFun1, liftFun2, bind_tc_ok]
  have : ¬ (r.start.val < r.«end».val) := by omega
  simp [this]

/-- Limb-level spec for `fe_add`: total (no panic) under the no-overflow
    hypothesis, and the output limbs are exactly the limbwise sums
    (no modular reduction, no carry propagation). -/
theorem add_limbs_spec (a b : Fe) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hbnd : a0.val + b0.val < 2^64 ∧ a1.val + b1.val < 2^64 ∧
            a2.val + b2.val < 2^64 ∧ a3.val + b3.val < 2^64 ∧
            a4.val + b4.val < 2^64) :
    fe_add a b ⦃ r => ∃ r0 r1 r2 r3 r4 : U64,
      (↑r : List U64) = [r0, r1, r2, r3, r4] ∧
      r0.val = a0.val + b0.val ∧ r1.val = a1.val + b1.val ∧
      r2.val = a2.val + b2.val ∧ r3.val = a3.val + b3.val ∧
      r4.val = a4.val + b4.val ⦄ := by
  obtain ⟨hbnd0, hbnd1, hbnd2, hbnd3, hbnd4⟩ := hbnd
  unfold fe_add
    Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51.add
    backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign
    backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop
  -- Iteration 1 (i = 0)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o1, iter1, ho1, hs1, he1⟩
  simp only [ho1]
  step as ⟨x1, hx1⟩
  step as ⟨y1, hy1⟩
  simp [ha, hb] at hx1 hy1
  step as ⟨v0, hv0⟩
  rw [hx1, hy1] at hv0
  step as ⟨s1, hd1⟩
  try simp only [spec_ok]
  -- Iteration 2 (i = 1)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o2, iter2, ho2, hs2, he2⟩
  simp only [ho2]
  step as ⟨x2, hx2⟩
  step as ⟨y2, hy2⟩
  simp [hd1, Array.set_val_eq, ha, hb, hs1, he1] at hx2 hy2
  step as ⟨v1, hv1⟩
  rw [hx2, hy2] at hv1
  step as ⟨s2, hd2⟩
  try simp only [spec_ok]
  -- Iteration 3 (i = 2)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o3, iter3, ho3, hs3, he3⟩
  simp only [ho3]
  step as ⟨x3, hx3⟩
  step as ⟨y3, hy3⟩
  simp [hd1, hd2, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2] at hx3 hy3
  step as ⟨v2, hv2⟩
  rw [hx3, hy3] at hv2
  step as ⟨s3, hd3⟩
  try simp only [spec_ok]
  -- Iteration 4 (i = 3)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o4, iter4, ho4, hs4, he4⟩
  simp only [ho4]
  step as ⟨x4, hx4⟩
  step as ⟨y4, hy4⟩
  simp [hd1, hd2, hd3, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2, hs3, he3] at hx4 hy4
  step as ⟨v3, hv3⟩
  rw [hx4, hy4] at hv3
  step as ⟨s4, hd4⟩
  try simp only [spec_ok]
  -- Iteration 5 (i = 4)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_lt_spec as ⟨o5, iter5, ho5, hs5, he5⟩
  simp only [ho5]
  step as ⟨x5, hx5⟩
  step as ⟨y5, hy5⟩
  simp [hd1, hd2, hd3, hd4, Array.set_val_eq, ha, hb, hs1, he1, hs2, he2, hs3, he3,
    hs4, he4] at hx5 hy5
  step as ⟨v4, hv4⟩
  rw [hx5, hy5] at hv4
  step as ⟨s5, hd5⟩
  try simp only [spec_ok]
  -- Iteration 6 (range exhausted: 5 ≥ 5)
  apply loop_step
  simp only [backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51.add_assign_loop.body]
  step with range_next_ge_spec as ⟨o6, iter6, ho6, hr6⟩
  simp only [ho6]
  try simp only [spec_ok]
  -- Final: exhibit the limbs
  refine ⟨v0, v1, v2, v3, v4, ?_, hv0, hv1, hv2, hv3, hv4⟩
  simp [hd1, hd2, hd3, hd4, hd5, Array.set_val_eq, ha, hs1, hs2, hs3, hs4]

/-- Main spec for `fe_add`: the output has 5 limbs, its (unreduced) value is
    the sum of the input values, and limb bounds double. -/
theorem add_spec (a b : Fe) (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : U64)
    (ha : (↑a : List U64) = [a0, a1, a2, a3, a4])
    (hb : (↑b : List U64) = [b0, b1, b2, b3, b4])
    (hbnd : a0.val + b0.val < 2^64 ∧ a1.val + b1.val < 2^64 ∧
            a2.val + b2.val < 2^64 ∧ a3.val + b3.val < 2^64 ∧
            a4.val + b4.val < 2^64) :
    fe_add a b ⦃ r => (↑r : List U64).length = 5 ∧
      feVal r = feVal a + feVal b ∧
      ∀ c, Bnd a c → Bnd b c → Bnd r (2*c) ⦄ := by
  apply spec_mono (add_limbs_spec a b a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 ha hb hbnd)
  rintro r ⟨r0, r1, r2, r3, r4, hr, h0, h1, h2, h3, h4⟩
  refine ⟨by simp [hr], ?_, ?_⟩
  · rw [feVal_eq r r0 r1 r2 r3 r4 hr, feVal_eq a a0 a1 a2 a3 a4 ha,
        feVal_eq b b0 b1 b2 b3 b4 hb]
    simp only [limbsVal]
    omega
  · intro c hA hB
    rw [Bnd_eq a a0 a1 a2 a3 a4 c ha] at hA
    rw [Bnd_eq b b0 b1 b2 b3 b4 c hb] at hB
    rw [Bnd_eq r r0 r1 r2 r3 r4 (2*c) hr]
    omega

end CurveFieldProofs
