import Mathlib

namespace Erdos271.KernelMass

theorem kernel_formula :
∀ K : Real → Real, (∀ v : Real, K v = Real.exp (-3 * v / 2) / (2 - Real.exp (-v)) ^ 3) → MeasureTheory.IntegrableOn K (Set.Ioi 0) MeasureTheory.volume ∧ MeasureTheory.integral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) K = 3 / 8 - Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2) :=
by
  intro K hK
  have primitive_derivative :
    ∀ H : Real → Real → Real, (∀ r : Real, ∀ t : Real, H r t = (1 / 2) * (t / (2 - t ^ 2) ^ 2) - (1 / 8) * (t / (2 - t ^ 2)) - (1 / (16 * r)) * (Real.log (r + t) - Real.log (r - t))) → ∀ r : Real, ∀ t : Real, 1 < r → r ^ 2 = 2 → 0 ≤ t → t ≤ 1 → HasDerivAt (H r) (2 * t ^ 2 / (2 - t ^ 2) ^ 3) t :=
    by
      intro H hH r t hr hr2 ht0 ht1
      have hr0 : r ≠ 0 := ne_of_gt (by linarith)
      have hdpos : 0 < 2 - t ^ 2 := by
        have hp := mul_nonneg (sub_nonneg.mpr ht1) (by linarith : 0 ≤ 1 + t)
        nlinarith
      have hd : 2 - t ^ 2 ≠ 0 := ne_of_gt hdpos
      have hp : r + t ≠ 0 := ne_of_gt (by linarith)
      have hm : r - t ≠ 0 := ne_of_gt (by linarith)
      have hlogalg : 1 / (r + t) + 1 / (r - t) = 2 * r / (2 - t ^ 2) := by
        have heq : 2 - t ^ 2 = (r + t) * (r - t) := by nlinarith [hr2]
        rw [heq]
        field_simp [hp, hm]
        <;> ring
      have hden : HasDerivAt (fun x : Real => 2 - x ^ 2) (-2 * t) t := by
        exact ((hasDerivAt_const t (2 : Real)).sub
          ((hasDerivAt_id t).fun_pow 2)).congr_deriv (by norm_num <;> ring)
      have hlog : HasDerivAt
          (fun x : Real => Real.log (r + x) - Real.log (r - x))
          (2 * r / (2 - t ^ 2)) t := by
        have hp' := ((hasDerivAt_const t r).add (hasDerivAt_id t)).log hp
        have hm' := ((hasDerivAt_const t r).sub (hasDerivAt_id t)).log hm
        have hs := hp'.sub hm'
        have hvalue : (0 + 1 : Real) / (r + t) - (0 - 1 : Real) / (r - t) =
            2 * r / (2 - t ^ 2) := by
          simpa only [zero_add, zero_sub, neg_div, sub_neg_eq_add] using hlogalg
        exact hs.congr_deriv (by
          change (0 + 1 : Real) / (r + t) - (0 - 1 : Real) / (r - t) =
            2 * r / (2 - t ^ 2)
          exact hvalue)
      have ha := (hasDerivAt_id t).div (hden.pow 2) (pow_ne_zero 2 hd)
      have hb := (hasDerivAt_id t).div hden hd
      have hc := ((ha.const_mul (1 / 2 : Real)).sub
        (hb.const_mul (1 / 8 : Real))).sub (hlog.const_mul (1 / (16 * r)))
      rw [show H r = (fun x : Real => (1 / 2) * (x / (2 - x ^ 2) ^ 2) -
          (1 / 8) * (x / (2 - x ^ 2)) -
          (1 / (16 * r)) * (Real.log (r + x) - Real.log (r - x))) from funext (hH r)]
      exact hc.congr_deriv (by dsimp; field_simp [hr0, hd] <;> ring)
  let r : Real := Real.sqrt 2
  have hr2 : r ^ 2 = (2 : Real) := Real.sq_sqrt (by norm_num)
  have hr : (1 : Real) < r := by
    have hnon : 0 ≤ r := Real.sqrt_nonneg 2
    nlinarith
  have hr0 : r ≠ 0 := ne_of_gt (by linarith)
  let H : Real → Real → Real := fun r t =>
    (1 / 2) * (t / (2 - t ^ 2) ^ 2) - (1 / 8) * (t / (2 - t ^ 2)) -
    (1 / (16 * r)) * (Real.log (r + t) - Real.log (r - t))
  have hdH (t : Real) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      HasDerivAt (H r) (2 * t ^ 2 / (2 - t ^ 2) ^ 3) t :=
    primitive_derivative H (by intro r t; rfl) r t hr hr2 ht0 ht1
  have hH0 : H r 0 = 0 := by simp [H]
  have hH1 : H r 1 = 3 / 8 - Real.log (1 + r) / (8 * r) := by
    have hm : r - 1 ≠ 0 := ne_of_gt (by linarith)
    have hp : r + 1 ≠ 0 := ne_of_gt (by linarith)
    have hprod : (r - 1) * (r + 1) = 1 := by nlinarith [hr2]
    have hlog : Real.log (r - 1) + Real.log (r + 1) = 0 := by
      rw [← Real.log_mul hm hp, hprod, Real.log_one]
    have hlog' : Real.log (r - 1) = -Real.log (r + 1) := by linarith
    dsimp [H]
    norm_num
    rw [hlog', show 1 + r = r + 1 by ring]
    field_simp [hr0]
    <;> ring
  let F : Real → Real := fun v => -H r (Real.exp (-v / 2))
  have hdF : ∀ v ∈ Set.Ici (0 : Real), HasDerivAt F (K v) v := by
    intro v hv
    have hv0 : 0 ≤ v := hv
    have he0 : 0 ≤ Real.exp (-v / 2) := (Real.exp_pos _).le
    have he1 : Real.exp (-v / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have he2 : Real.exp (-v / 2) ^ 2 = Real.exp (-v) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have he3 : Real.exp (-v / 2) ^ 3 = Real.exp (-3 * v / 2) := by
      calc
        _ = Real.exp (-v / 2) * Real.exp (-v / 2) * Real.exp (-v / 2) := by ring
        _ = Real.exp ((-v / 2) + (-v / 2) + (-v / 2)) := by
          rw [Real.exp_add, Real.exp_add]
        _ = _ := by congr 1; ring
    have hcomp := ((hdH _ he0 he1).comp v
      (((hasDerivAt_id v).neg.div_const 2).exp)).neg
    apply hcomp.congr_deriv
    change -(2 * Real.exp (-v / 2) ^ 2 / (2 - Real.exp (-v / 2) ^ 2) ^ 3 *
      (Real.exp (-v / 2) * (-(1 : Real) / 2))) = K v
    calc
      _ = Real.exp (-v / 2) ^ 3 / (2 - Real.exp (-v / 2) ^ 2) ^ 3 := by ring
      _ = K v := by rw [he2, he3, hK v]
  have hpos : ∀ v ∈ Set.Ioi (0 : Real), 0 ≤ K v := by
    intro v hv
    have hv0 : 0 ≤ v := le_of_lt hv
    have he : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [hK v]
    apply div_nonneg (Real.exp_nonneg _)
    exact pow_nonneg (by linarith : 0 ≤ 2 - Real.exp (-v)) 3
  have hx : Filter.Tendsto (fun v : Real => v / 2) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num : (0 : Real) < 2) Filter.tendsto_id
  have he : Filter.Tendsto (fun v : Real => Real.exp (-v / 2)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hx
  have hlimit : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have ht := (((hdH 0 (by norm_num) (by norm_num)).continuousAt.tendsto).comp he).neg
    simpa only [F, Function.comp_def, Pi.neg_apply, hH0, neg_zero] using ht
  constructor
  · exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hdF hpos hlimit
  · have hf := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hdF hpos hlimit
    have hF0 : F 0 = -H r 1 := by simp [F]
    rw [hF0, zero_sub, neg_neg, hH1] at hf
    exact hf

end Erdos271.KernelMass

#print axioms Erdos271.KernelMass.kernel_formula
