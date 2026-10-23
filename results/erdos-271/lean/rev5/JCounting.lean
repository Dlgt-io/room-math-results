import FinitePrefix

namespace Erdos271.FiniteIntegrals

theorem cutoff_indicator :
∀ a : Real, ∀ b : Real, ∀ f : Real → Real, 0 < a → a ≤ b → IntervalIntegrable f MeasureTheory.volume a b → IntervalIntegrable (Set.indicator (Set.Ici a) f) MeasureTheory.volume 0 b ∧ intervalIntegral (Set.indicator (Set.Ici a) f) 0 b MeasureTheory.volume = intervalIntegral f a b MeasureTheory.volume := by
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

theorem counting_double_integral :
∀ P : Finset Real, ∀ X : Real, ∀ H : Real → Real → Real, ∀ A : Real → Real, ∀ K : Real → Real → Real, ∀ B : Real → Real, ∀ G : Real → Real → Real, 0 < X → (∀ p : Real, Membership.mem P p → 0 < p ∧ p ≤ X) → (∀ p : Real, H p = Set.indicator (Set.Ici p) (Function.const Real (1 : Real))) → (∀ t : Real, A t = Finset.sum P (Function.swap H t)) → (∀ t : Real, ∀ u : Real, K t u = A u * A t / (2 * t - u) ^ 3) → (∀ t : Real, B t = intervalIntegral (K t) 0 t MeasureTheory.volume) → (∀ p : Real, ∀ q : Real, G p q = 1 / (2 * max p q) - 1 / (2 * X) + 1 / (4 * (2 * X - p)) - 1 / (4 * (2 * max p q - p))) → IntervalIntegrable B MeasureTheory.volume 0 X ∧ intervalIntegral B 0 X MeasureTheory.volume = Finset.sum P (Function.comp (Finset.sum P) G) := by
  have basic := reciprocal_integrals
  have nested := nested_pair_integral
  have cutoff := cutoff_indicator
  classical
  intro P X H A K B G hX hP hH hA hK hB hG
  let c : Real → Real → Real := fun t u => 1 / (2 * t - u) ^ 3
  let R : Real → Real → Real := fun p t => intervalIntegral (c t) p t MeasureTheory.volume
  let V : Real → Real → Real → Real :=
    fun p q => Set.indicator (Set.Ici (max p q)) (R p)
  have hV : ∀ p ∈ P, ∀ q ∈ P,
      IntervalIntegrable (V p q) MeasureTheory.volume 0 X ∧
      intervalIntegral (V p q) 0 X MeasureTheory.volume = G p q := by
    intro p hp q hq
    have hm0 : 0 < max p q := lt_of_lt_of_le (hP p hp).1 (le_max_left p q)
    have hmX : max p q ≤ X := max_le (hP p hp).2 (hP q hq).2
    have hn := nested p (max p q) X c (R p) (hP p hp).1
      (le_max_left p q) hmX (fun t u => rfl) (fun t => rfl)
    have hc := cutoff (max p q) X (R p) hm0 hmX hn.1
    refine ⟨hc.1, ?_⟩
    rw [hc.2, hn.2, hG p q]
  have hpair : ∀ p ∈ P, ∀ q ∈ P, ∀ t : Real, 0 ≤ t →
      IntervalIntegrable (fun u => H p u * H q t / (2 * t - u) ^ 3)
        MeasureTheory.volume 0 t ∧
      intervalIntegral (fun u => H p u * H q t / (2 * t - u) ^ 3)
        0 t MeasureTheory.volume = V p q t := by
    intro p hp q hq t ht
    by_cases hqt : q ≤ t
    · have hqv : H q t = 1 := by
        rw [hH q]
        simp [Set.indicator, hqt]
      by_cases hpt : p ≤ t
      · have hi := (basic.2 p t (c t) (hP p hp).1 hpt (fun u => rfl)).1
        have hc := cutoff p t (c t) (hP p hp).1 hpt hi
        have heq : (fun u => H p u * H q t / (2 * t - u) ^ 3) =
            Set.indicator (Set.Ici p) (c t) := by
          funext u
          rw [hqv, hH p]
          by_cases hpu : p ≤ u <;> simp [c, Set.indicator, hpu]
        rw [heq]
        refine ⟨hc.1, ?_⟩
        rw [hc.2]
        simp [V, R, Set.indicator, max_le_iff, hpt, hqt]
      · have hz : Set.EqOn
            (fun u => H p u * H q t / (2 * t - u) ^ 3)
            (fun _ : Real => (0 : Real)) (Set.uIcc 0 t) := by
          intro u hu
          rw [Set.uIcc_of_le ht] at hu
          have hpu : ¬ p ≤ u := by linarith [hu.2]
          rw [hH p]
          simp [Set.indicator, hpu]
        have hi : IntervalIntegrable (fun u => H p u * H q t / (2 * t - u) ^ 3)
            MeasureTheory.volume 0 t := by
          apply IntervalIntegrable.congr _
            (intervalIntegrable_const : IntervalIntegrable (fun _ : Real => (0 : Real)) MeasureTheory.volume 0 t)
          intro u hu
          have hu' : u ∈ Set.uIcc 0 t := by
            rw [Set.uIcc_of_le ht]
            rw [Set.uIoc_of_le ht] at hu
            exact ⟨hu.1.le, hu.2⟩
          exact (hz hu').symm
        refine ⟨hi, ?_⟩
        rw [intervalIntegral.integral_congr hz]
        simp [V, Set.indicator, max_le_iff, hpt]
    · have hqv : H q t = 0 := by
        rw [hH q]
        simp [Set.indicator, hqt]
      have heq : (fun u => H p u * H q t / (2 * t - u) ^ 3) =
          (fun _ : Real => (0 : Real)) := by
        funext u
        simp [hqv]
      rw [heq]
      constructor
      · exact intervalIntegrable_const
      · simp [V, Set.indicator, max_le_iff, hqt]
  have hKfun (t : Real) : K t = fun u => P.sum (fun p => P.sum
      (fun q => H p u * H q t / (2 * t - u) ^ 3)) := by
    funext u
    rw [hK t u, hA u, hA t]
    change (P.sum (fun p => H p u) * P.sum (fun q => H q t)) / (2 * t - u) ^ 3 = _
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, Finset.sum_div]
  have hBval : ∀ t : Real, 0 ≤ t →
      B t = P.sum (fun p => P.sum (fun q => V p q t)) := by
    intro t ht
    have hrow : ∀ p ∈ P, IntervalIntegrable
        (fun u => P.sum (fun q => H p u * H q t / (2 * t - u) ^ 3))
        MeasureTheory.volume 0 t := by
      intro p hp
      simpa only [Finset.sum_fn] using
        (IntervalIntegrable.sum P (fun q hq => (hpair p hp q hq t ht).1))
    rw [hB t, hKfun t, intervalIntegral.integral_finsetSum hrow]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum (fun q hq => (hpair p hp q hq t ht).1)]
    apply Finset.sum_congr rfl
    intro q hq
    exact (hpair p hp q hq t ht).2
  have hrow : ∀ p ∈ P, IntervalIntegrable
      (fun t => P.sum (fun q => V p q t)) MeasureTheory.volume 0 X := by
    intro p hp
    simpa only [Finset.sum_fn] using
      (IntervalIntegrable.sum P (fun q hq => (hV p hp q hq).1))
  have hsum : IntervalIntegrable
      (fun t => P.sum (fun p => P.sum (fun q => V p q t)))
      MeasureTheory.volume 0 X := by
    simpa only [Finset.sum_fn] using (IntervalIntegrable.sum P hrow)
  have hBeq : Set.EqOn B (fun t => P.sum (fun p => P.sum (fun q => V p q t)))
      (Set.uIcc 0 X) := by
    intro t ht
    rw [Set.uIcc_of_le hX.le] at ht
    exact hBval t ht.1
  have hiB : IntervalIntegrable B MeasureTheory.volume 0 X := by
    apply IntervalIntegrable.congr _ hsum
    intro t ht
    have ht' : t ∈ Set.uIcc 0 X := by
      rw [Set.uIcc_of_le hX.le]
      rw [Set.uIoc_of_le hX.le] at ht
      exact ⟨ht.1.le, ht.2⟩
    exact (hBeq ht').symm
  refine ⟨hiB, ?_⟩
  rw [intervalIntegral.integral_congr hBeq, intervalIntegral.integral_finsetSum hrow]
  change P.sum (fun p => intervalIntegral
    (fun t => P.sum (fun q => V p q t)) 0 X MeasureTheory.volume) =
      P.sum (fun p => P.sum (fun q => G p q))
  apply Finset.sum_congr rfl
  intro p hp
  rw [intervalIntegral.integral_finsetSum (fun q hq => (hV p hp q hq).1)]
  apply Finset.sum_congr rfl
  intro q hq
  exact (hV p hp q hq).2

end Erdos271.FiniteIntegrals
