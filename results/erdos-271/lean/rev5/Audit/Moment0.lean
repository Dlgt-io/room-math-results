import Mathlib

namespace Erdos271.RoundTwo

theorem FirstMoment_checked :
∀ (K M : Real → Real), (∀ v, K v = Real.exp (-3 * v / 2) / (2 - Real.exp (-v)) ^ 3) → (∀ v, M v = v * K v) → MeasureTheory.IntegrableOn M (Set.Ioi 0) MeasureTheory.volume ∧ 0 ≤ MeasureTheory.integral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) M ∧ MeasureTheory.integral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) M ≤ 2 :=
by
  intro K M hK hM
  have hmeas : Measurable M := by
    have heq : M = fun v : Real => v * (Real.exp (-3 * v / 2) / (2 - Real.exp (-v)) ^ 3) := by
      funext v
      rw [hM v, hK v]
    rw [heq]
    fun_prop
  have hbound : ∀ v : Real, 0 ≤ v → 0 ≤ M v ∧ M v ≤ 2 * Real.exp (-v) := by
    intro v hv
    have he : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
    have hd : 1 ≤ 2 - Real.exp (-v) := by linarith
    have hd0 : 0 ≤ 2 - Real.exp (-v) := by linarith
    have hd2 : 1 ≤ (2 - Real.exp (-v)) ^ 2 := by
      nlinarith [sq_nonneg (2 - Real.exp (-v) - 1)]
    have hd3 : 1 ≤ (2 - Real.exp (-v)) ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg (2 - Real.exp (-v)))]
    have hk0 : 0 ≤ K v := by
      rw [hK v]
      exact div_nonneg (Real.exp_nonneg _) (pow_nonneg hd0 _)
    have hk1 : K v ≤ Real.exp (-3 * v / 2) := by
      rw [hK v]
      exact div_le_self (Real.exp_nonneg _) hd3
    have hvexp : v ≤ 2 * Real.exp (v / 2) := by
      have h := Real.add_one_le_exp (v / 2)
      linarith
    have hex : Real.exp (v / 2) * Real.exp (-3 * v / 2) = Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    constructor
    · rw [hM v]
      exact mul_nonneg hv hk0
    · calc
        M v = v * K v := hM v
        _ ≤ v * Real.exp (-3 * v / 2) := mul_le_mul_of_nonneg_left hk1 hv
        _ ≤ (2 * Real.exp (v / 2)) * Real.exp (-3 * v / 2) := mul_le_mul_of_nonneg_right hvexp (Real.exp_nonneg _)
        _ = 2 * Real.exp (-v) := by rw [mul_assoc, hex]
  have hg : MeasureTheory.IntegrableOn (fun v : Real => 2 * Real.exp (-v)) (Set.Ioi 0) MeasureTheory.volume :=
    (integrableOn_exp_neg_Ioi 0).const_mul 2
  have hmi : MeasureTheory.IntegrableOn M (Set.Ioi 0) MeasureTheory.volume := by
    apply hg.mono' hmeas.aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    have hb := hbound v (le_of_lt hv)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  refine ⟨hmi, ?_, ?_⟩
  · apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
    exact (hbound v (le_of_lt hv)).1
  · have hcmp := MeasureTheory.integral_mono_ae hmi hg (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with v hv
      exact (hbound v (le_of_lt hv)).2)
    have hgi : MeasureTheory.integral (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) (fun v : Real => 2 * Real.exp (-v)) = 2 := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero]
      ring
    rw [hgi] at hcmp
    exact hcmp

end Erdos271.RoundTwo

#print axioms Erdos271.RoundTwo.FirstMoment_checked
