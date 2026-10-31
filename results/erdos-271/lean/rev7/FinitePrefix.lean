import Mathlib
namespace Erdos271.FiniteIntegrals

theorem reciprocal_integrals :
(∀ a : Real, ∀ b : Real, ∀ f : Real → Real, 0 < a → a ≤ b → (∀ t : Real, f t = 1 / t ^ 2) → IntervalIntegrable f MeasureTheory.volume a b ∧ intervalIntegral f a b MeasureTheory.volume = 1 / a - 1 / b) ∧ (∀ p : Real, ∀ t : Real, ∀ f : Real → Real, 0 < p → p ≤ t → (∀ u : Real, f u = 1 / (2 * t - u) ^ 3) → IntervalIntegrable f MeasureTheory.volume p t ∧ intervalIntegral f p t MeasureTheory.volume = 1 / (2 * t ^ 2) - 1 / (2 * (2 * t - p) ^ 2)) :=
by
  constructor
  · intro a b f ha hab hf
    have hf' : f = (fun t : Real => 1 / t ^ 2) := funext hf
    subst f
    have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact lt_of_lt_of_le ha ht.1
    have hc : ContinuousOn (fun t : Real => 1 / t ^ 2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (hpos t ht))
    refine ⟨hc.intervalIntegrable, ?_⟩
    have hn : (0 : Real) ∉ Set.uIcc a b := by
      intro hh
      exact (lt_irrefl 0) (hpos 0 hh)
    have hz := integral_zpow (a := a) (b := b) (n := (-2 : Int))
      (Or.inr ⟨by norm_num, hn⟩)
    norm_num [zpow_neg, one_div] at hz
    convert hz using 1 <;> simp only [one_div] <;> ring
  · intro p t f hp hpt hf
    have hf' : f = (fun u : Real => 1 / (2 * t - u) ^ 3) := funext hf
    subst f
    have hpos : ∀ u ∈ Set.uIcc p t, 0 < 2 * t - u := by
      intro u hu
      rw [Set.uIcc_of_le hpt] at hu
      linarith [hu.2]
    have hc : ContinuousOn (fun u : Real => 1 / (2 * t - u) ^ 3) (Set.uIcc p t) := by
      apply ContinuousOn.div continuousOn_const
        ((continuousOn_const.sub continuousOn_id).pow 3)
      intro u hu
      exact pow_ne_zero 3 (ne_of_gt (hpos u hu))
    refine ⟨hc.intervalIntegrable, ?_⟩
    have ht : 0 < t := lt_of_lt_of_le hp hpt
    have hn : (0 : Real) ∉ Set.uIcc t (2 * t - p) := by
      rw [Set.uIcc_of_le (by linarith : t ≤ 2 * t - p)]
      intro hh
      linarith [hh.1]
    have hz := integral_zpow (a := t) (b := 2 * t - p) (n := (-3 : Int))
      (Or.inr ⟨by norm_num, hn⟩)
    norm_num [zpow_neg, one_div] at hz
    have hs := intervalIntegral.integral_comp_sub_left
      (a := p) (b := t) (fun u : Real => 1 / u ^ 3) (2 * t)
    rw [show 2 * t - t = t by ring] at hs
    rw [hs]
    have hpower : (fun u : Real => 1 / u ^ 3) = (fun u : Real => (u ^ 3)⁻¹) := by
      funext u
      rw [one_div]
    rw [hpower]
    rw [hz]
    simp only [one_div, mul_inv_rev]
    norm_num
    <;> ring

theorem nested_pair_integral :
∀ p : Real, ∀ M : Real, ∀ X : Real, ∀ K : Real → Real → Real, ∀ F : Real → Real, 0 < p → p ≤ M → M ≤ X → (∀ t : Real, ∀ u : Real, K t u = 1 / (2 * t - u) ^ 3) → (∀ t : Real, F t = intervalIntegral (K t) p t MeasureTheory.volume) → IntervalIntegrable F MeasureTheory.volume M X ∧ intervalIntegral F M X MeasureTheory.volume = 1 / (2 * M) - 1 / (2 * X) + 1 / (4 * (2 * X - p)) - 1 / (4 * (2 * M - p)) := by
  have basic := reciprocal_integrals
  intro p M X K F hp hpM hMX hK hF
  let g : Real → Real := fun t => (1 / 2 : Real) * (1 / t ^ 2) -
    (1 / 2 : Real) * (1 / (2 * t - p) ^ 2)
  have hpos : ∀ t ∈ Set.uIcc M X, 0 < t ∧ 0 < 2 * t - p := by
    intro t ht
    rw [Set.uIcc_of_le hMX] at ht
    constructor <;> linarith [ht.1]
  have hi1 := (basic.1 M X (fun t : Real => 1 / t ^ 2)
    (lt_of_lt_of_le hp hpM) hMX (fun t => rfl)).1
  have hc2 : ContinuousOn (fun t : Real => 1 / (2 * t - p) ^ 2) (Set.uIcc M X) := by
    apply ContinuousOn.div continuousOn_const
      (((continuousOn_const.mul continuousOn_id).sub continuousOn_const).pow 2)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (hpos t ht).2)
  have hi2 : IntervalIntegrable (fun t : Real => 1 / (2 * t - p) ^ 2) MeasureTheory.volume M X := hc2.intervalIntegrable
  have hig : IntervalIntegrable g MeasureTheory.volume M X :=
    (hi1.const_mul (1 / 2 : Real)).sub (hi2.const_mul (1 / 2 : Real))
  have heq : Set.EqOn F g (Set.uIcc M X) := by
    intro t ht
    have hpt : p ≤ t := by
      rw [Set.uIcc_of_le hMX] at ht
      exact hpM.trans ht.1
    rw [hF t, (basic.2 p t (K t) hp hpt (hK t)).2]
    dsimp [g]
    simp only [one_div, mul_inv_rev]
    norm_num
    <;> ring
  have hiF : IntervalIntegrable F MeasureTheory.volume M X := by
    apply IntervalIntegrable.congr _ hig
    intro t ht
    have ht' : t ∈ Set.uIcc M X := by
      rw [Set.uIcc_of_le hMX]
      rw [Set.uIoc_of_le hMX] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact (heq ht').symm
  refine ⟨hiF, ?_⟩
  rw [intervalIntegral.integral_congr heq]
  have hval1 := (basic.1 M X (fun t : Real => 1 / t ^ 2)
    (lt_of_lt_of_le hp hpM) hMX (fun t => rfl)).2
  have hval2 : intervalIntegral (fun t : Real => 1 / (2 * t - p) ^ 2)
      M X MeasureTheory.volume =
      (1 / 2 : Real) * (1 / (2 * M - p) - 1 / (2 * X - p)) := by
    have hs := intervalIntegral.integral_comp_mul_sub
      (a := M) (b := X) (fun u : Real => 1 / u ^ 2)
      (by norm_num : (2 : Real) ≠ 0) p
    have hv := (basic.1 (2 * M - p) (2 * X - p)
      (fun u : Real => 1 / u ^ 2) (by linarith) (by linarith) (fun u => rfl)).2
    rw [hv] at hs
    simpa only [smul_eq_mul, one_div] using hs
  dsimp [g]
  rw [intervalIntegral.integral_sub (hi1.const_mul (1 / 2 : Real))
      (hi2.const_mul (1 / 2 : Real))]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hval1, hval2]
  simp only [one_div, mul_inv_rev]
  norm_num
  <;> ring

end Erdos271.FiniteIntegrals


namespace Erdos271.FiniteIntegrals

theorem counting_square_integral :
∀ P : Finset Real, ∀ X : Real, ∀ H : Real → Real → Real, ∀ A : Real → Real, ∀ f : Real → Real, ∀ G : Real → Real → Real, 0 < X → (∀ p : Real, Membership.mem P p → 0 < p ∧ p ≤ X) → (∀ p : Real, H p = Set.indicator (Set.Ici p) (Function.const Real (1 : Real))) → (∀ t : Real, A t = Finset.sum P (Function.swap H t)) → (∀ t : Real, f t = A t ^ 2 / t ^ 2) → (∀ p : Real, ∀ q : Real, G p q = 1 / max p q - 1 / X) → IntervalIntegrable f MeasureTheory.volume 0 X ∧ intervalIntegral f 0 X MeasureTheory.volume = Finset.sum P (Function.comp (Finset.sum P) G) :=
by
  have cutoff : ∀ a : Real, ∀ b : Real, ∀ f : Real → Real, 0 < a → a ≤ b → IntervalIntegrable f MeasureTheory.volume a b → IntervalIntegrable (Set.indicator (Set.Ici a) f) MeasureTheory.volume 0 b ∧ intervalIntegral (Set.indicator (Set.Ici a) f) 0 b MeasureTheory.volume = intervalIntegral f a b MeasureTheory.volume := by
    intro a b f ha hab hi
    have hb : 0 ≤ b := le_trans ha.le hab
    have hinter : Set.Ici a ∩ Set.Icc (0 : Real) b = Set.Icc a b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨hax, h0x, hxb⟩
        exact ⟨hax, hxb⟩
      · rintro ⟨hax, hxb⟩
        exact ⟨hax, ha.le.trans hax, hxb⟩
    have hi' : MeasureTheory.IntegrableOn f (Set.Icc a b) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
    have hcut : IntervalIntegrable (Set.indicator (Set.Ici a) f) MeasureTheory.volume 0 b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
      rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet, hinter]
      exact hi'
    refine ⟨hcut, ?_⟩
    rw [intervalIntegral.integral_of_le hb, intervalIntegral.integral_of_le hab]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
    have hinter' : Set.Ioc (0 : Real) b ∩ Set.Ici a = Set.Icc a b := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨⟨h0x, hxb⟩, hax⟩
        exact ⟨hax, hxb⟩
      · rintro ⟨hax, hxb⟩
        exact ⟨⟨ha.trans_le hax, hxb⟩, hax⟩
    rw [hinter', MeasureTheory.integral_Icc_eq_integral_Ioc]
  have square : ∀ a : Real, ∀ b : Real, ∀ f : Real → Real, 0 < a → a ≤ b → (∀ t : Real, f t = 1 / t ^ 2) → IntervalIntegrable f MeasureTheory.volume a b ∧ intervalIntegral f a b MeasureTheory.volume = 1 / a - 1 / b := by
    intro a b f ha hab hf
    have hf' : f = (fun t : Real => 1 / t ^ 2) := funext hf
    subst f
    have hpos : ∀ t ∈ Set.uIcc a b, 0 < t := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact lt_of_lt_of_le ha ht.1
    have hc : ContinuousOn (fun t : Real => 1 / t ^ 2) (Set.uIcc a b) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro t ht
      exact pow_ne_zero 2 (ne_of_gt (hpos t ht))
    refine ⟨hc.intervalIntegrable, ?_⟩
    have hn : (0 : Real) ∉ Set.uIcc a b := by
      intro hh
      exact (lt_irrefl 0) (hpos 0 hh)
    have hz := integral_zpow (a := a) (b := b) (n := (-2 : Int))
      (Or.inr ⟨by norm_num, hn⟩)
    norm_num [zpow_neg, one_div] at hz
    convert hz using 1 <;> simp only [one_div] <;> ring
  classical
  intro P X H A f G hX hP hH hA hf hG
  let base : Real → Real := fun t => 1 / t ^ 2
  let V : Real → Real → Real → Real :=
    fun p q => Set.indicator (Set.Ici (max p q)) base
  have hV : ∀ p ∈ P, ∀ q ∈ P,
      IntervalIntegrable (V p q) MeasureTheory.volume 0 X ∧
      intervalIntegral (V p q) 0 X MeasureTheory.volume =
        1 / max p q - 1 / X := by
    intro p hp q hq
    have hm0 : 0 < max p q := lt_of_lt_of_le (hP p hp).1 (le_max_left p q)
    have hmX : max p q ≤ X := max_le (hP p hp).2 (hP q hq).2
    have hb := square (max p q) X base hm0 hmX (fun t => rfl)
    have hc := cutoff (max p q) X base hm0 hmX hb.1
    exact ⟨hc.1, hc.2.trans hb.2⟩
  have hfun : f = fun t => P.sum (fun p => P.sum (fun q => V p q t)) := by
    funext t
    rw [hf t, hA t, pow_two]
    change (P.sum (fun p => H p t) * P.sum (fun q => H q t)) / t ^ 2 = _
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hH p, hH q]
    by_cases hpt : p ≤ t <;> by_cases hqt : q ≤ t <;>
      simp [V, base, Set.indicator, hpt, hqt, max_le_iff]
  have hrow : ∀ p ∈ P, IntervalIntegrable
      (fun t => P.sum (fun q => V p q t)) MeasureTheory.volume 0 X := by
    intro p hp
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum P (fun q hq => (hV p hp q hq).1))
  have hsum : IntervalIntegrable
      (fun t => P.sum (fun p => P.sum (fun q => V p q t)))
      MeasureTheory.volume 0 X := by
    simpa only [Finset.sum_fn] using (IntervalIntegrable.sum P hrow)
  rw [hfun]
  refine ⟨hsum, ?_⟩
  rw [intervalIntegral.integral_finsetSum hrow]
  change P.sum (fun p => intervalIntegral
    (fun t => P.sum (fun q => V p q t)) 0 X MeasureTheory.volume) =
      P.sum (fun p => P.sum (fun q => G p q))
  apply Finset.sum_congr rfl
  intro p hp
  rw [intervalIntegral.integral_finsetSum (fun q hq => (hV p hp q hq).1)]
  apply Finset.sum_congr rfl
  intro q hq
  rw [(hV p hp q hq).2, hG p q]

end Erdos271.FiniteIntegrals
