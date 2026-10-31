module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Finset.Range
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-!
# Reviewed statement vocabulary

This file and Mathlib are the entire import closure of `Challenge.lean`.
The counting function includes zero and is zero when the interval is empty.
-/

namespace Erdos271

/-- The number of members of `S` in the real interval `[0, x]`. -/
noncomputable def F (S : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x < 0 then 0 else
    (((Finset.range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S)).card : ℝ)

/-- Every sufficiently large non-member has two earlier forward-covering witnesses. -/
def WeaklyAP3Covering (S : Set ℕ) : Prop :=
  ∃ s : ℕ, ∀ z : ℕ, s < z → z ∉ S →
    ∃ a ∈ S, ∃ b ∈ S, a < b ∧ b < z ∧ z = 2 * b - a

end Erdos271
