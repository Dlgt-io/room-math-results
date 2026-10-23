import Audit.Glue4K

/-!
# Lemma 4 glue, part II: the counting function on a logarithmic window

* range lemmas `I_range`, `J_range` (copied verbatim from `RangeK.lean`, inside a namespace,
  because `RangeK.lean` redeclares the top-level `Acount`/`Kker` of `LogSub.lean`);
* `hfun_meas`, `hfun_nonneg`, `hfun_le`, `hfun_env`: `h = A(e^t) e^{-t/2}` is measurable,
  `0 ≤ h ≤ #P` on `[0, ∞)`, and the envelope `L√x ≤ A(x) ≤ U√x` on `[x0, X]` gives
  `L ≤ h ≤ U` on `[log x0, log X]`;
* `J_drop`: for `0 ≤ g ≤ B` on `[0, T]`, the iterated `J`-form over the window `[t0, T]` is
  at most the one over `[0, T]`.
-/

open MeasureTheory Set Real

namespace Erdos271.Glue

lemma Acount_eq_zero_of_lt (P : Finset ℝ) (hP : ∀ p ∈ P, 1 ≤ p) {t : ℝ} (ht : t < 1) :
    Acount P t = 0 := by
  unfold Acount
  refine Finset.sum_eq_zero (fun p hp => ?_)
  have : t ∉ Ici p := fun h => by have := hP p hp; simp only [mem_Ici] at h; linarith
  simp [this]

/-- Range lemma: for P ⊂ [1,∞), the I- and J-integrals over (0,X) equal those over (1,X). -/
theorem I_range (P : Finset ℝ) (hP : ∀ p ∈ P, 1 ≤ p) (X : ℝ) :
    ∫ x in Ioo 0 X, Acount P x ^ 2 / x ^ 2 = ∫ x in Ioo 1 X, Acount P x ^ 2 / x ^ 2 := by
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (Ioo_subset_Ioo_left zero_le_one) ?_
  filter_upwards [Measure.ae_ne volume 1] with x hx1 hx
  have hlt : x < 1 := by
    rcases hx with ⟨⟨_, hxX⟩, hn⟩
    by_contra h
    exact hn ⟨lt_of_le_of_ne (not_lt.mp h) (Ne.symm hx1), hxX⟩
  simp [Acount_eq_zero_of_lt P hP hlt]

theorem J_range (P : Finset ℝ) (hP : ∀ p ∈ P, 1 ≤ p) (X : ℝ) :
    ∫ x in Ioo 0 X, Acount P x * ∫ u in Ioo 0 x, Acount P u / (2 * x - u) ^ 3
      = ∫ x in Ioo 1 X, Acount P x * ∫ u in Ioo 1 x, Acount P u / (2 * x - u) ^ 3 := by
  -- inner range first, pointwise in x > 0
  have inner : ∀ x, 0 < x →
      ∫ u in Ioo 0 x, Acount P u / (2 * x - u) ^ 3
        = ∫ u in Ioo 1 x, Acount P u / (2 * x - u) ^ 3 := by
    intro x hx
    by_cases h1 : 1 ≤ x
    · refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
        (Ioo_subset_Ioo_left zero_le_one) ?_
      filter_upwards [Measure.ae_ne volume 1] with u hu1 hu
      have hlt : u < 1 := by
        rcases hu with ⟨⟨_, huX⟩, hn⟩
        by_contra h
        exact hn ⟨lt_of_le_of_ne (not_lt.mp h) (Ne.symm hu1), huX⟩
      simp [Acount_eq_zero_of_lt P hP hlt]
    · have hx1 : x < 1 := lt_of_not_ge h1
      rw [Ioo_eq_empty (by linarith : ¬ (1:ℝ) < x)]
      simp only [Measure.restrict_empty, integral_zero_measure]
      refine setIntegral_eq_zero_of_forall_eq_zero (fun u hu => ?_)
      simp [Acount_eq_zero_of_lt P hP (lt_trans hu.2 hx1)]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => by rw [inner x hx.1])]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (Ioo_subset_Ioo_left zero_le_one) ?_
  filter_upwards [Measure.ae_ne volume 1] with x hx1 hx
  have hlt : x < 1 := by
    rcases hx with ⟨⟨_, hxX⟩, hn⟩
    by_contra h
    exact hn ⟨lt_of_le_of_ne (not_lt.mp h) (Ne.symm hx1), hxX⟩
  simp [Acount_eq_zero_of_lt P hP hlt]

theorem hfun_meas (P : Finset ℝ) : Measurable (hfun (Acount P)) := by
  unfold hfun
  exact ((Acount_measurable P).comp measurable_exp).mul (by fun_prop)

theorem hfun_nonneg (P : Finset ℝ) (t : ℝ) : 0 ≤ hfun (Acount P) t :=
  mul_nonneg (Acount_nonneg _ _) (exp_pos _).le

theorem hfun_le (P : Finset ℝ) {t : ℝ} (ht : 0 ≤ t) : hfun (Acount P) t ≤ P.card := by
  unfold hfun
  have h0 := Acount_le P (exp t)
  have h1 : exp (-(t / 2)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  calc Acount P (exp t) * exp (-(t / 2)) ≤ (P.card : ℝ) * 1 :=
        mul_le_mul h0 h1 (exp_pos _).le (Nat.cast_nonneg _)
    _ = P.card := mul_one _

theorem hfun_env (P : Finset ℝ) {L U x0 X : ℝ} (hx0 : 0 < x0) (hxX : x0 ≤ X)
    (henv : ∀ x ∈ Icc x0 X, L * √x ≤ Acount P x ∧ Acount P x ≤ U * √x) :
    ∀ t ∈ Icc (log x0) (log X), L ≤ hfun (Acount P) t ∧ hfun (Acount P) t ≤ U := by
  intro t ht
  have hX : 0 < X := lt_of_lt_of_le hx0 hxX
  have hx : exp t ∈ Icc x0 X := by
    constructor
    · rw [← exp_log hx0]; exact exp_le_exp.mpr ht.1
    · rw [← exp_log hX]; exact exp_le_exp.mpr ht.2
  obtain ⟨h1, h2⟩ := henv _ hx
  rw [← exp_half] at h1 h2
  have he : exp (t / 2) * exp (-(t / 2)) = 1 := by rw [← exp_add]; simp
  have hp := exp_pos (-(t / 2))
  unfold hfun
  constructor
  · have := mul_le_mul_of_nonneg_right h1 hp.le
    rw [mul_assoc, he, mul_one] at this; exact this
  · have := mul_le_mul_of_nonneg_right h2 hp.le
    rw [mul_assoc, he, mul_one] at this; exact this

/-- The inner integral is strongly measurable in the outer variable. -/
theorem inner_smeas {K g : ℝ → ℝ} (hK : Measurable K) (hg : Measurable g) (a : ℝ) :
    StronglyMeasurable (fun τ => ∫ σ in Ioo a τ, K (τ - σ) * g σ) := by
  set S : Set (ℝ × ℝ) := {p | a < p.2 ∧ p.2 < p.1} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have hf : StronglyMeasurable (S.indicator (fun p : ℝ × ℝ => K (p.1 - p.2) * g p.2)) :=
    (((hK.comp (measurable_fst.sub measurable_snd)).mul (hg.comp measurable_snd)).indicator
      hS).stronglyMeasurable
  have e : (fun τ => ∫ σ in Ioo a τ, K (τ - σ) * g σ)
      = fun τ => ∫ σ, S.indicator (fun p : ℝ × ℝ => K (p.1 - p.2) * g p.2) (τ, σ) := by
    funext τ
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
  rw [e]
  exact hf.integral_prod_right' (ν := volume)

/-- Bounds for the inner integral. -/
theorem inner_bounds {g : ℝ → ℝ} (hg : Measurable g) {B T a τ : ℝ} (ha : 0 ≤ a)
    (hT : 0 ≤ T) (hτ : τ ≤ T) (hg0 : ∀ x, 0 ≤ x → x ≤ T → 0 ≤ g x ∧ g x ≤ B) :
    IntegrableOn (fun σ => Kker (τ - σ) * g σ) (Ioo a τ) volume ∧
    0 ≤ ∫ σ in Ioo a τ, Kker (τ - σ) * g σ ∧
    ∫ σ in Ioo a τ, Kker (τ - σ) * g σ ≤ B * T := by
  have hmem : ∀ σ ∈ Ioo a τ, 0 ≤ Kker (τ - σ) * g σ ∧ Kker (τ - σ) * g σ ≤ B := by
    intro σ hσ
    have k := Erdos271.Lemma4.Kker_bounds (by linarith [hσ.2] : 0 ≤ τ - σ)
    have gg := hg0 σ (by linarith [hσ.1]) (by linarith [hσ.2])
    exact ⟨mul_nonneg k.1 gg.1, by nlinarith⟩
  have hmeas : Measurable (fun σ => Kker (τ - σ) * g σ) :=
    (Erdos271.Lemma4.Kker_measurable.comp (measurable_const.sub measurable_id)).mul hg
  have hint : IntegrableOn (fun σ => Kker (τ - σ) * g σ) (Ioo a τ) volume :=
    Measure.integrableOn_of_bounded (M := B) measure_Ioo_lt_top.ne hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hmem σ hσ).1]; exact (hmem σ hσ).2))
  refine ⟨hint, setIntegral_nonneg measurableSet_Ioo (fun σ hσ => (hmem σ hσ).1), ?_⟩
  by_cases hat : a ≤ τ
  · have hB : 0 ≤ B := by
      have := hg0 0 le_rfl (by linarith); linarith
    calc ∫ σ in Ioo a τ, Kker (τ - σ) * g σ ≤ ∫ σ in Ioo a τ, B :=
          setIntegral_mono_on hint (integrableOn_const measure_Ioo_lt_top.ne)
            measurableSet_Ioo (fun σ hσ => (hmem σ hσ).2)
      _ = B * (τ - a) := by
          rw [setIntegral_const, Real.volume_real_Ioo_of_le hat, smul_eq_mul, mul_comm]
      _ ≤ B * T := mul_le_mul_of_nonneg_left (by linarith) hB
  · rw [Ioo_eq_empty (by intro h; exact hat h.le)]
    simp only [Measure.restrict_empty, integral_zero_measure]
    have := hg0 0 le_rfl (by linarith)
    nlinarith

theorem outer_int {g : ℝ → ℝ} (hg : Measurable g) {B T a : ℝ} (ha : 0 ≤ a)
    (hg0 : ∀ x, 0 ≤ x → x ≤ T → 0 ≤ g x ∧ g x ≤ B) :
    IntegrableOn (fun t => g t * ∫ u in Ioo a t, Kker (t - u) * g u) (Ioo a T) volume ∧
    ∀ t ∈ Ioo a T, 0 ≤ g t * ∫ u in Ioo a t, Kker (t - u) * g u := by
  have hmeas : AEStronglyMeasurable (fun t => g t * ∫ u in Ioo a t, Kker (t - u) * g u)
      volume :=
    (hg.stronglyMeasurable.mul (inner_smeas Erdos271.Lemma4.Kker_measurable hg a)).aestronglyMeasurable
  have hpt : ∀ t ∈ Ioo a T, 0 ≤ g t * ∫ u in Ioo a t, Kker (t - u) * g u ∧
      g t * ∫ u in Ioo a t, Kker (t - u) * g u ≤ B * (B * T) := by
    intro t ht
    have gg := hg0 t (by linarith [ht.1]) ht.2.le
    have ib := inner_bounds hg (a := a) (τ := t) ha (by linarith [ht.1, ht.2]) ht.2.le hg0
    exact ⟨mul_nonneg gg.1 ib.2.1, mul_le_mul gg.2 ib.2.2 ib.2.1 (le_trans gg.1 gg.2)⟩
  refine ⟨Measure.integrableOn_of_bounded (M := B * (B * T)) measure_Ioo_lt_top.ne hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpt t ht).1]; exact (hpt t ht).2)),
    fun t ht => (hpt t ht).1⟩

/-- **Dropping the initial range of `J`.** -/
theorem J_drop {g : ℝ → ℝ} (hg : Measurable g) {B t0 T : ℝ} (ht0 : 0 ≤ t0)
    (hg0 : ∀ x, 0 ≤ x → x ≤ T → 0 ≤ g x ∧ g x ≤ B) :
    ∫ t in Ioo t0 T, g t * ∫ u in Ioo t0 t, Kker (t - u) * g u
      ≤ ∫ t in Ioo 0 T, g t * ∫ u in Ioo 0 t, Kker (t - u) * g u := by
  obtain ⟨iw, _⟩ := outer_int hg (a := t0) ht0 hg0
  obtain ⟨if0, nf0⟩ := outer_int hg (a := 0) le_rfl hg0
  calc ∫ t in Ioo t0 T, g t * ∫ u in Ioo t0 t, Kker (t - u) * g u
      ≤ ∫ t in Ioo t0 T, g t * ∫ u in Ioo 0 t, Kker (t - u) * g u := by
        refine setIntegral_mono_on iw (if0.mono_set (Ioo_subset_Ioo_left ht0))
          measurableSet_Ioo (fun t ht => ?_)
        have gg := hg0 t (by linarith [ht.1]) ht.2.le
        refine mul_le_mul_of_nonneg_left ?_ gg.1
        have i0 := inner_bounds hg (a := 0) (τ := t) le_rfl (by linarith [ht.1, ht.2]) ht.2.le hg0
        exact setIntegral_mono_set i0.1
          (ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ =>
            mul_nonneg (Erdos271.Lemma4.Kker_bounds (by linarith [hσ.2])).1
              (hg0 σ (by linarith [hσ.1]) (by linarith [hσ.2, ht.2])).1))
          (Filter.Eventually.of_forall (Ioo_subset_Ioo_left ht0))
    _ ≤ ∫ t in Ioo 0 T, g t * ∫ u in Ioo 0 t, Kker (t - u) * g u :=
        setIntegral_mono_set if0 (ae_restrict_of_forall_mem measurableSet_Ioo nf0)
          (Filter.Eventually.of_forall (Ioo_subset_Ioo_left ht0))

end Erdos271.Glue
