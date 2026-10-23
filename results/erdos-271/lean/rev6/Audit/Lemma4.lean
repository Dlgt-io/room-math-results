import Mathlib

/-!
# Writeup Lemma 4 (positivity lemma), integral level — reduction to two kernel facts

Setting: `h` measurable with `L ≤ h ≤ U` on `[0, τ]`; `K` measurable, `0 ≤ K ≤ KM` on `[0, τ]`.
Triangle `T τ = {(t, u) : 0 ≤ u ≤ t ≤ τ}` with Lebesgue measure on `ℝ × ℝ`.
`Q h = ∫_T K(t-u) h(t) h(u)`, `D = ∫_0^τ (U - h)`.

Proved here:
* `sq_integral_bound`: `∫_0^τ h² ≤ U² τ - (L+U) D`;
* `Q_lower`: `Q h ≥ U² Q1 - U C1 - U C2` with `Q1 = ∫_T K(t-u)`, `C1 = ∫_T K(t-u)(U-h t)`,
  `C2 = ∫_T K(t-u)(U-h u)`;
* `lemma4_of_kernel_bounds`: Lemma 4 assuming the kernel facts
  `Q1 ≥ β τ - η`, `C1 ≤ β D`, `C2 ≤ β D` (these need Fubini + the kernel mass; not proved here).
-/

open MeasureTheory Set intervalIntegral

namespace Erdos271.Lemma4

/-- The triangle `{(t,u) : 0 ≤ u ≤ t ≤ τ}`. -/
def T (τ : ℝ) : Set (ℝ × ℝ) := {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ τ}

theorem T_meas (τ : ℝ) : MeasurableSet (T τ) := by
  unfold T
  refine (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const))

theorem T_sub (τ : ℝ) : T τ ⊆ Icc 0 τ ×ˢ Icc 0 τ := by
  rintro ⟨t, u⟩ ⟨h1, h2, h3⟩
  exact ⟨⟨le_trans h1 h2, h3⟩, ⟨h1, le_trans h2 h3⟩⟩

theorem T_finite (τ : ℝ) : (volume : Measure (ℝ × ℝ)) (T τ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono (T_sub τ))
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (by simp) (by simp)

/-- Bounded measurable functions are integrable on the triangle. -/
theorem integrableOn_T {f : ℝ × ℝ → ℝ} (hf : Measurable f) (τ M : ℝ)
    (hM : ∀ p ∈ T τ, |f p| ≤ M) : IntegrableOn f (T τ) volume :=
  Measure.integrableOn_of_bounded (T_finite τ) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem (T_meas τ) (fun p hp => by
      rw [Real.norm_eq_abs]; exact hM p hp))

/-- Bounded measurable functions are interval integrable on `[0, τ]`. -/
theorem iInt_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {τ : ℝ} (hτ : 0 ≤ τ) (M : ℝ)
    (hM : ∀ x ∈ Icc 0 τ, |f x| ≤ M) : IntervalIntegrable f volume 0 τ := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ]
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => by
      rw [Real.norm_eq_abs]; exact hM x (Ioc_subset_Icc_self hx)))

theorem abs_le_of_bounds {L U x : ℝ} (h1 : L ≤ x) (h2 : x ≤ U) : |x| ≤ |L| + |U| := by
  rw [abs_le]; constructor
  · have := neg_abs_le L; have := abs_nonneg U; linarith
  · have := le_abs_self U; have := abs_nonneg L; linarith

/-- **Square-integral bound** `∫_0^τ h² ≤ U² τ - (L+U) ∫_0^τ (U - h)`. -/
theorem sq_integral_bound {h : ℝ → ℝ} (hm : Measurable h) {L U τ : ℝ} (hτ : 0 ≤ τ)
    (hb : ∀ x ∈ Icc 0 τ, L ≤ h x ∧ h x ≤ U) :
    ∫ x in (0:ℝ)..τ, h x ^ 2 ≤ U ^ 2 * τ - (L + U) * ∫ x in (0:ℝ)..τ, (U - h x) := by
  have hB : ∀ x ∈ Icc 0 τ, |h x| ≤ |L| + |U| := fun x hx =>
    abs_le_of_bounds (hb x hx).1 (hb x hx).2
  have hi : IntervalIntegrable h volume 0 τ := iInt_of_bounded hm hτ _ hB
  have hi2 : IntervalIntegrable (fun x => h x ^ 2) volume 0 τ :=
    iInt_of_bounded (hm.pow_const 2) hτ ((|L| + |U|) ^ 2) (fun x hx => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x hx) 2)
  have hmono : ∫ x in (0:ℝ)..τ, h x ^ 2 ≤ ∫ x in (0:ℝ)..τ, ((L + U) * h x - L * U) := by
    apply integral_mono_on hτ hi2 ((hi.const_mul _).sub intervalIntegrable_const)
    intro x hx
    obtain ⟨h1, h2⟩ := hb x hx
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have e1 : ∫ x in (0:ℝ)..τ, ((L + U) * h x - L * U)
      = (L + U) * (∫ x in (0:ℝ)..τ, h x) - L * U * τ := by
    rw [integral_sub (hi.const_mul _) intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp; ring
  have e2 : ∫ x in (0:ℝ)..τ, (U - h x) = U * τ - ∫ x in (0:ℝ)..τ, h x := by
    rw [integral_sub intervalIntegrable_const hi, intervalIntegral.integral_const]; simp; ring
  rw [e2]; rw [e1] at hmono; nlinarith [hmono]

/-- Common hypotheses for the triangle estimates. -/
structure Hyp (K h : ℝ → ℝ) (L U τ KM : ℝ) : Prop where
  hKm : Measurable K
  hm : Measurable h
  hK0 : ∀ v, 0 ≤ v → v ≤ τ → 0 ≤ K v
  hKM : ∀ v, 0 ≤ v → v ≤ τ → K v ≤ KM
  hb : ∀ x ∈ Icc 0 τ, L ≤ h x ∧ h x ≤ U

theorem kdiff_bounds {K h : ℝ → ℝ} {L U τ KM : ℝ} (H : Hyp K h L U τ KM) {p : ℝ × ℝ}
    (hp : p ∈ T τ) :
    0 ≤ K (p.1 - p.2) ∧ K (p.1 - p.2) ≤ KM ∧ p.1 ∈ Icc 0 τ ∧ p.2 ∈ Icc 0 τ := by
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨H.hK0 _ (by linarith) (by linarith), H.hKM _ (by linarith) (by linarith),
    ⟨by linarith, h3⟩, ⟨h1, by linarith⟩⟩

/-- **Pointwise-to-integral step for `Q`.**
`∫_T K(t-u) h t h u ≥ U² ∫_T K(t-u) - U ∫_T K(t-u)(U - h t) - U ∫_T K(t-u)(U - h u)`. -/
theorem Q_lower {K h : ℝ → ℝ} {L U τ KM : ℝ} (H : Hyp K h L U τ KM) :
    U ^ 2 * (∫ p in T τ, K (p.1 - p.2))
      - U * (∫ p in T τ, K (p.1 - p.2) * (U - h p.1))
      - U * (∫ p in T τ, K (p.1 - p.2) * (U - h p.2))
      ≤ ∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2 := by
  have hKmp : Measurable (fun p : ℝ × ℝ => K (p.1 - p.2)) :=
    H.hKm.comp (measurable_fst.sub measurable_snd)
  have hh1 : Measurable (fun p : ℝ × ℝ => h p.1) := H.hm.comp measurable_fst
  have hh2 : Measurable (fun p : ℝ × ℝ => h p.2) := H.hm.comp measurable_snd
  set B := |L| + |U| with hBdef
  have hB : ∀ x ∈ Icc 0 τ, |h x| ≤ B := fun x hx =>
    abs_le_of_bounds (H.hb x hx).1 (H.hb x hx).2
  have hKabs : ∀ p ∈ T τ, |K (p.1 - p.2)| ≤ KM := by
    intro p hp; obtain ⟨k0, k1, -, -⟩ := kdiff_bounds H hp
    rw [abs_of_nonneg k0]; exact k1
  have hdB : ∀ x ∈ Icc 0 τ, |U - h x| ≤ |U| + B := fun x hx => by
    have := hB x hx
    calc |U - h x| ≤ |U| + |h x| := abs_sub _ _
      _ ≤ |U| + B := by linarith
  have i0 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2)) (T τ) volume :=
    integrableOn_T hKmp τ KM hKabs
  have i1 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.1)) (T τ) volume :=
    integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.1))
      (hKmp.mul (measurable_const.sub hh1)) τ (KM * (|U| + B)) (fun p hp => by
      obtain ⟨-, -, ht, -⟩ := kdiff_bounds H hp
      show |K (p.1 - p.2) * (U - h p.1)| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hKabs p hp) (hdB _ ht) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hKabs p hp)))
  have i2 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.2)) (T τ) volume :=
    integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.2))
      (hKmp.mul (measurable_const.sub hh2)) τ (KM * (|U| + B)) (fun p hp => by
      obtain ⟨-, -, -, hu⟩ := kdiff_bounds H hp
      show |K (p.1 - p.2) * (U - h p.2)| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hKabs p hp) (hdB _ hu) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hKabs p hp)))
  have i3 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * h p.1 * h p.2) (T τ) volume :=
    integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * h p.1 * h p.2)
      ((hKmp.mul hh1).mul hh2) τ (KM * B * B) (fun p hp => by
      obtain ⟨-, -, ht, hu⟩ := kdiff_bounds H hp
      show |K (p.1 - p.2) * h p.1 * h p.2| ≤ _
      rw [abs_mul, abs_mul]
      have hk := hKabs p hp
      have hb1 := hB _ ht
      have hb2 := hB _ hu
      have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb1
      exact mul_le_mul (mul_le_mul hk hb1 (abs_nonneg _) (le_trans (abs_nonneg _) hk)) hb2
        (abs_nonneg _) (mul_nonneg (le_trans (abs_nonneg _) hk) hB0))
  have hA : IntegrableOn (fun p : ℝ × ℝ => U ^ 2 * K (p.1 - p.2)
      - U * (K (p.1 - p.2) * (U - h p.1))) (T τ) volume :=
    (i0.const_mul _).sub (i1.const_mul _)
  have hA2 : IntegrableOn (fun p : ℝ × ℝ => U ^ 2 * K (p.1 - p.2)
      - U * (K (p.1 - p.2) * (U - h p.1)) - U * (K (p.1 - p.2) * (U - h p.2))) (T τ) volume :=
    hA.sub (i2.const_mul _)
  have hlin : U ^ 2 * (∫ p in T τ, K (p.1 - p.2))
      - U * (∫ p in T τ, K (p.1 - p.2) * (U - h p.1))
      - U * (∫ p in T τ, K (p.1 - p.2) * (U - h p.2))
      = ∫ p in T τ, (U ^ 2 * K (p.1 - p.2) - U * (K (p.1 - p.2) * (U - h p.1))
          - U * (K (p.1 - p.2) * (U - h p.2))) := by
    rw [integral_sub hA (i2.const_mul _), integral_sub (i0.const_mul _) (i1.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hlin]
  apply setIntegral_mono_on hA2 i3 (T_meas τ)
  intro p hp
  obtain ⟨k0, -, ht, hu⟩ := kdiff_bounds H hp
  have d1 : 0 ≤ U - h p.1 := sub_nonneg.mpr (H.hb _ ht).2
  have d2 : 0 ≤ U - h p.2 := sub_nonneg.mpr (H.hb _ hu).2
  have key : K (p.1 - p.2) * ((U - h p.1) * (U - h p.2)) ≥ 0 :=
    mul_nonneg k0 (mul_nonneg d1 d2)
  nlinarith [key]

/-- **Lemma 4, conditional on the two kernel facts.**
With `α = 3/2 - 4β`, `κ = 2αU - (3/2)(U - L)`, `D = ∫_0^τ (U - h)` and
`Q = ∫_T K(t-u) h(t) h(u)`: if `U ≥ 0`, `∫_T K(t-u) ≥ βτ - η`,
`∫_T K(t-u)(U - h t) ≤ β D` and `∫_T K(t-u)(U - h u) ≤ β D`, then
`(3/2) ∫_0^τ h² - 4 Q ≤ α U² τ - κ D + 4 U² η`. -/
theorem lemma4_of_kernel_bounds {K h : ℝ → ℝ} {L U τ KM β η : ℝ} (H : Hyp K h L U τ KM)
    (hτ : 0 ≤ τ) (hU : 0 ≤ U)
    (hQ1 : β * τ - η ≤ ∫ p in T τ, K (p.1 - p.2))
    (hC1 : ∫ p in T τ, K (p.1 - p.2) * (U - h p.1) ≤ β * ∫ x in (0:ℝ)..τ, (U - h x))
    (hC2 : ∫ p in T τ, K (p.1 - p.2) * (U - h p.2) ≤ β * ∫ x in (0:ℝ)..τ, (U - h x)) :
    (3 / 2) * (∫ x in (0:ℝ)..τ, h x ^ 2) - 4 * (∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * τ
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in (0:ℝ)..τ, (U - h x))
        + 4 * U ^ 2 * η := by
  have ha := sq_integral_bound H.hm hτ H.hb
  have hq := Q_lower H
  set D := ∫ x in (0:ℝ)..τ, (U - h x)
  set Q1 := ∫ p in T τ, K (p.1 - p.2)
  set C1 := ∫ p in T τ, K (p.1 - p.2) * (U - h p.1)
  set C2 := ∫ p in T τ, K (p.1 - p.2) * (U - h p.2)
  have hU2 : 0 ≤ U ^ 2 := sq_nonneg U
  have s1 : U ^ 2 * (β * τ - η) ≤ U ^ 2 * Q1 := mul_le_mul_of_nonneg_left hQ1 hU2
  have s2 : U * C1 ≤ U * (β * D) := mul_le_mul_of_nonneg_left hC1 hU
  have s3 : U * C2 ≤ U * (β * D) := mul_le_mul_of_nonneg_left hC2 hU
  nlinarith [ha, hq, s1, s2, s3]

end Erdos271.Lemma4

#print axioms Erdos271.Lemma4.sq_integral_bound
#print axioms Erdos271.Lemma4.Q_lower
#print axioms Erdos271.Lemma4.lemma4_of_kernel_bounds
