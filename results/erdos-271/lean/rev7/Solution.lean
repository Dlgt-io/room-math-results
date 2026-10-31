import Abstract

namespace Erdos271

/-- The abstract's lower bound, with an inclusive count and extended nonnegative limsup. -/
theorem main_result (S : Set ℕ) (hS : WeaklyAP3Covering S) :
    ENNReal.ofReal (Real.sqrt (2 * Real.sqrt 2 / Real.log (1 + Real.sqrt 2))) ≤
      Filter.limsup (fun x : ℝ => ENNReal.ofReal (F S x / Real.sqrt x))
        Filter.atTop :=
  Abstract.inclusive_limsup S hS

end Erdos271
