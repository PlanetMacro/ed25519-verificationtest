/- Demonstration proofs over the Aeneas-generated `Smoke` model.
   This is the *template* for verifying real code: state a spec as a Hoare-style
   triple over the generated `Result`-monad function, then discharge it with
   Aeneas' `step`/`progress`/`grind` tactics. -/
import Smoke
open Aeneas Std Result

namespace smoke

/-- Correctness of `add`: when `x + y` does not overflow a `u32`, the function
    succeeds and returns exactly `x + y`. -/
theorem add_spec (x y : U32) (h : x.val + y.val ≤ U32.max) :
    add x y ⦃ z => z.val = x.val + y.val ⦄ := by
  unfold add
  step as ⟨ z ⟩
  grind

end smoke
