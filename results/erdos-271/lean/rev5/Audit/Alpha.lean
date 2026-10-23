import Mathlib

/-!
# Numerical bound `α > 25/81` for `α = log(1+√2)/(2√2)`

From the artanh series `log(1+y) - log(1-y) = ∑ 2 y^{2k+1}/(2k+1)` at `y = √2/2`, where
`(1+y)/(1-y) = (1+√2)^2`. Five terms give `α ≥ (1 + 1/6 + 1/20 + 1/56 + 1/144)/4 > 25/81`.
Consequences: `α > 3/10` and `1/√α < 9/5`.
-/

open Real

namespace Erdos271.Alpha

/-- `α = log(1+√2)/(2√2)`. -/
noncomputable def α : ℝ := Real.log (1 + √2) / (2 * √2)

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem log_one_add_sqrt2_ge :
    (√2 / 2) * (1 + 1/6 + 1/20 + 1/56 + 1/144) ≤ Real.log (1 + √2) := by
  set y : ℝ := √2 / 2 with hy
  have hs0 : 0 < √2 := by positivity
  have hs1 : √2 < 2 := by nlinarith [sqrt2_sq]
  have hy0 : 0 < y := by positivity
  have hy1 : |y| < 1 := by rw [abs_of_pos hy0]; linarith
  have hy2 : y ^ 2 = 1 / 2 := by rw [hy, div_pow, sqrt2_sq]; norm_num
  have hH := hasSum_log_sub_log_of_abs_lt_one hy1
  have hS := sum_le_hasSum (Finset.range 5)
    (fun i _ => by positivity) hH
  have hpow : ∀ k : ℕ, y ^ (2 * k + 1) = y * (1 / 2) ^ k := by
    intro k; rw [pow_succ, pow_mul, hy2, mul_comm]
  simp only [hpow, Finset.sum_range_succ, Finset.sum_range_zero] at hS
  -- log(1+y) - log(1-y) = 2 log(1+√2)
  have h1 : 0 < 1 - y := by linarith
  have hq : (1 + y) / (1 - y) = (1 + √2) ^ 2 := by
    rw [div_eq_iff h1.ne']
    rw [hy]; ring_nf; rw [show (√2 : ℝ) ^ 3 = √2 ^ 2 * √2 by ring, sqrt2_sq]; ring
  have hl : Real.log (1 + y) - Real.log (1 - y) = 2 * Real.log (1 + √2) := by
    rw [← Real.log_div (by linarith) h1.ne', hq, Real.log_pow]; push_cast; ring
  rw [hl] at hS
  norm_num at hS
  linarith

theorem alpha_gt : (25 : ℝ) / 81 < α := by
  have h := log_one_add_sqrt2_ge
  have hs0 : 0 < √2 := by positivity
  unfold α
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

theorem alpha_gt_three_tenths : (3 : ℝ) / 10 < α := by
  have := alpha_gt; linarith

theorem alpha_pos : 0 < α := by
  have := alpha_gt; linarith

/-- `C_* = 1/√α < 9/5`. -/
theorem Cstar_lt : 1 / √α < 9 / 5 := by
  have ha := alpha_gt
  have hsa : 5 / 9 < √α := by
    rw [show (5 : ℝ) / 9 = √(25 / 81) by
      rw [show (25 : ℝ) / 81 = (5 / 9) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) ha
  rw [div_lt_iff₀ (by linarith)]
  linarith

end Erdos271.Alpha
