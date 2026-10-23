import Mathlib
import Audit.Lemma4

open MeasureTheory Set

namespace Erdos271.Lemma4

/-- **Triangle Fubini.** `∫_T F = ∫_{t ∈ [0,τ]} ∫_{u ∈ [0,t]} F(t,u)`. -/
theorem tri_iter {τ : ℝ} {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F (T τ) volume) :
    ∫ p in T τ, F p = ∫ t in Icc 0 τ, ∫ u in Icc 0 t, F (t, u) := by
  rw [← integral_indicator (T_meas τ)]
  have hI : Integrable ((T τ).indicator F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hF.integrable_indicator (T_meas τ)
  rw [Measure.volume_eq_prod, integral_prod _ hI]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  ext t
  by_cases ht : t ≤ τ
  · by_cases h0 : 0 ≤ t
    · rw [indicator_of_mem (show t ∈ Icc 0 τ from ⟨h0, ht⟩)]
      rw [← integral_indicator measurableSet_Icc]
      congr 1; ext u
      simp only [indicator, T, mem_ofPred_eq, mem_Icc]
      by_cases hu : 0 ≤ u ∧ u ≤ t
      · simp [hu.1, hu.2, ht]
      · have : ¬ (0 ≤ u ∧ u ≤ t ∧ t ≤ τ) := fun h => hu ⟨h.1, h.2.1⟩
        simp only [this, hu, ite_false]
    · rw [indicator_of_notMem (show t ∉ Icc 0 τ from fun h => h0 h.1)]
      have : ∀ u, (T τ).indicator F (t, u) = 0 := by
        intro u
        apply indicator_of_notMem
        rintro ⟨h1, h2, -⟩
        exact h0 (le_trans h1 h2)
      simp [this]
  · rw [indicator_of_notMem (show t ∉ Icc 0 τ from fun h => ht h.2)]
    have : ∀ u, (T τ).indicator F (t, u) = 0 := by
      intro u
      apply indicator_of_notMem
      rintro ⟨-, -, h3⟩
      exact ht h3
    simp [this]

/-- **Triangle Fubini, other order.** `∫_T F = ∫_{u ∈ [0,τ]} ∫_{t ∈ [u,τ]} F(t,u)`. -/
theorem tri_iter_swap {τ : ℝ} {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F (T τ) volume) :
    ∫ p in T τ, F p = ∫ u in Icc 0 τ, ∫ t in Icc u τ, F (t, u) := by
  rw [← integral_indicator (T_meas τ)]
  have hI : Integrable ((T τ).indicator F) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hF.integrable_indicator (T_meas τ)
  rw [Measure.volume_eq_prod, integral_prod_symm _ hI]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  ext u
  by_cases hu : 0 ≤ u ∧ u ≤ τ
  · rw [indicator_of_mem (show u ∈ Icc 0 τ from hu)]
    rw [← integral_indicator measurableSet_Icc]
    congr 1; ext t
    simp only [indicator, T, mem_ofPred_eq, mem_Icc]
    by_cases ht : u ≤ t ∧ t ≤ τ
    · simp [ht.1, ht.2, hu.1]
    · simp only [ht, and_false, ↓reduceIte]
  · rw [indicator_of_notMem (show u ∉ Icc 0 τ from hu)]
    have : ∀ t, (T τ).indicator F (t, u) = 0 := by
      intro t
      apply indicator_of_notMem
      rintro ⟨h1, h2, h3⟩
      exact hu ⟨h1, le_trans h2 h3⟩
    simp [this]

theorem iInt_eq_Icc {f : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ x in (0:ℝ)..τ, f x = ∫ x in Icc 0 τ, f x := by
  rw [intervalIntegral.integral_of_le hτ, integral_Icc_eq_integral_Ioc]

/-- Shared step: if `F(t,u) = K(t-u) g(t)` (`C1`) or `K(t-u) g(u)` (`C2`), the inner kernel
integral is at most `β`, and `g ≥ 0` is bounded measurable, then `∫_T ≤ β ∫_0^τ g`. -/
theorem outer_bound {g m : ℝ → ℝ} {τ β : ℝ} (hτ : 0 ≤ τ) (hg : Measurable g) (G : ℝ)
    (hgb : ∀ x ∈ Icc 0 τ, 0 ≤ g x ∧ g x ≤ G) (hm0 : ∀ x ∈ Icc 0 τ, 0 ≤ m x)
    (hmβ : ∀ x ∈ Icc 0 τ, m x ≤ β) :
    ∫ x in Icc 0 τ, g x * m x ≤ β * ∫ x in (0:ℝ)..τ, g x := by
  rw [iInt_eq_Icc hτ, ← MeasureTheory.integral_const_mul]
  have hgi : IntegrableOn (fun x => β * g x) (Icc 0 τ) volume := by
    refine Measure.integrableOn_of_bounded (M := |β| * G) (by simp)
      (hg.const_mul β).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgb x hx).1]
    exact mul_le_mul_of_nonneg_left (hgb x hx).2 (abs_nonneg _)
  apply integral_mono_of_nonneg _ hgi
  · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => by
      have := hgb x hx
      show g x * m x ≤ β * g x
      nlinarith [hmβ x hx, this.1])
  · exact ae_restrict_of_forall_mem measurableSet_Icc (fun x hx =>
      mul_nonneg (hgb x hx).1 (hm0 x hx))

/-- **`C1 ≤ β D`**, given `∫_{u∈[0,t]} K(t-u) ≤ β` for `t ∈ [0,τ]`. -/
theorem C1_le {K h : ℝ → ℝ} {L U τ KM β : ℝ} (H : Hyp K h L U τ KM) (hτ : 0 ≤ τ)
    (hβ : ∀ t ∈ Icc 0 τ, ∫ u in Icc 0 t, K (t - u) ≤ β) :
    ∫ p in T τ, K (p.1 - p.2) * (U - h p.1) ≤ β * ∫ x in (0:ℝ)..τ, (U - h x) := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.1)) (T τ) volume := by
    have hKmp : Measurable (fun p : ℝ × ℝ => K (p.1 - p.2)) :=
      H.hKm.comp (measurable_fst.sub measurable_snd)
    refine integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.1))
      (hKmp.mul (measurable_const.sub (H.hm.comp measurable_fst))) τ (KM * (U - L))
      (fun p hp => ?_)
    obtain ⟨k0, k1, ht, -⟩ := kdiff_bounds H hp
    have := H.hb _ ht
    show |K (p.1 - p.2) * (U - h p.1)| ≤ _
    rw [abs_mul, abs_of_nonneg k0, abs_of_nonneg (by linarith)]
    exact mul_le_mul k1 (by linarith) (by linarith) (le_trans k0 k1)
  rw [tri_iter hint]
  have hinner : ∀ t, ∫ u in Icc 0 t, K (t - u) * (U - h t)
      = (U - h t) * ∫ u in Icc 0 t, K (t - u) := by
    intro t; rw [MeasureTheory.integral_mul_const, mul_comm]
  simp_rw [hinner]
  refine outer_bound hτ (measurable_const.sub H.hm) (U - L)
    (fun x hx => ⟨by linarith [(H.hb x hx).2], by linarith [(H.hb x hx).1]⟩) ?_ hβ
  intro t ht
  apply setIntegral_nonneg measurableSet_Icc
  intro u hu
  exact H.hK0 _ (by linarith [hu.2]) (by linarith [hu.1, ht.2])

/-- **`C2 ≤ β D`**, given `∫_{t∈[u,τ]} K(t-u) ≤ β` for `u ∈ [0,τ]`. -/
theorem C2_le {K h : ℝ → ℝ} {L U τ KM β : ℝ} (H : Hyp K h L U τ KM) (hτ : 0 ≤ τ)
    (hβ : ∀ u ∈ Icc 0 τ, ∫ t in Icc u τ, K (t - u) ≤ β) :
    ∫ p in T τ, K (p.1 - p.2) * (U - h p.2) ≤ β * ∫ x in (0:ℝ)..τ, (U - h x) := by
  have hint : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.2)) (T τ) volume := by
    have hKmp : Measurable (fun p : ℝ × ℝ => K (p.1 - p.2)) :=
      H.hKm.comp (measurable_fst.sub measurable_snd)
    refine integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * (U - h p.2))
      (hKmp.mul (measurable_const.sub (H.hm.comp measurable_snd))) τ (KM * (U - L))
      (fun p hp => ?_)
    obtain ⟨k0, k1, -, hu⟩ := kdiff_bounds H hp
    have := H.hb _ hu
    show |K (p.1 - p.2) * (U - h p.2)| ≤ _
    rw [abs_mul, abs_of_nonneg k0, abs_of_nonneg (by linarith)]
    exact mul_le_mul k1 (by linarith) (by linarith) (le_trans k0 k1)
  rw [tri_iter_swap hint]
  have hinner : ∀ u, ∫ t in Icc u τ, K (t - u) * (U - h u)
      = (U - h u) * ∫ t in Icc u τ, K (t - u) := by
    intro u; rw [MeasureTheory.integral_mul_const, mul_comm]
  simp_rw [hinner]
  refine outer_bound hτ (measurable_const.sub H.hm) (U - L)
    (fun x hx => ⟨by linarith [(H.hb x hx).2], by linarith [(H.hb x hx).1]⟩) ?_ hβ
  intro u hu
  apply setIntegral_nonneg measurableSet_Icc
  intro t ht
  exact H.hK0 _ (by linarith [ht.1]) (by linarith [ht.2, hu.1])

/-- **Lemma 4, reduced to one-dimensional kernel facts and `Q1 ≥ βτ - η`.** -/
theorem lemma4_reduced {K h : ℝ → ℝ} {L U τ KM β η : ℝ} (H : Hyp K h L U τ KM)
    (hτ : 0 ≤ τ) (hU : 0 ≤ U)
    (hQ1 : β * τ - η ≤ ∫ p in T τ, K (p.1 - p.2))
    (hβ1 : ∀ t ∈ Icc 0 τ, ∫ u in Icc 0 t, K (t - u) ≤ β)
    (hβ2 : ∀ u ∈ Icc 0 τ, ∫ t in Icc u τ, K (t - u) ≤ β) :
    (3 / 2) * (∫ x in (0:ℝ)..τ, h x ^ 2) - 4 * (∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * τ
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in (0:ℝ)..τ, (U - h x))
        + 4 * U ^ 2 * η :=
  lemma4_of_kernel_bounds H hτ hU hQ1 (C1_le H hτ hβ1) (C2_le H hτ hβ2)

/-- `∫_{(0,s]} K ≤ ∫_{(0,∞)} K` for `K ≥ 0` on `(0,∞)`. -/
theorem partial_mass_le {K : ℝ → ℝ} {β s : ℝ} (hK0 : ∀ v, 0 < v → 0 ≤ K v)
    (hKi : IntegrableOn K (Ioi 0) volume) (hβ : ∫ v in Ioi 0, K v = β) :
    ∫ v in Ioc 0 s, K v ≤ β := by
  rw [← hβ]
  apply setIntegral_mono_set hKi
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => hK0 v hv)
  · exact Filter.Eventually.of_forall (fun v hv => (show v ∈ Ioi (0:ℝ) from hv.1))

/-- Inner kernel integral, `t`-outer order. -/
theorem inner1_le {K : ℝ → ℝ} {β t : ℝ} (ht : 0 ≤ t) (hK0 : ∀ v, 0 < v → 0 ≤ K v)
    (hKi : IntegrableOn K (Ioi 0) volume) (hβ : ∫ v in Ioi 0, K v = β) :
    ∫ u in Icc 0 t, K (t - u) ≤ β := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left, sub_self, sub_zero,
    intervalIntegral.integral_of_le ht]
  exact partial_mass_le hK0 hKi hβ

/-- Inner kernel integral, `u`-outer order. -/
theorem inner2_le {K : ℝ → ℝ} {β u τ : ℝ} (hu : u ≤ τ) (hK0 : ∀ v, 0 < v → 0 ≤ K v)
    (hKi : IntegrableOn K (Ioi 0) volume) (hβ : ∫ v in Ioi 0, K v = β) :
    ∫ t in Icc u τ, K (t - u) ≤ β := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu,
    intervalIntegral.integral_comp_sub_right, sub_self,
    intervalIntegral.integral_of_le (by linarith)]
  exact partial_mass_le hK0 hKi hβ

/-- **Lemma 4 from the kernel mass**: the only remaining hypothesis on the
double integral is `Q1 = ∫_T K(t-u) ≥ βτ - η`. -/
theorem lemma4_from_mass {K h : ℝ → ℝ} {L U τ KM β η : ℝ} (H : Hyp K h L U τ KM)
    (hτ : 0 ≤ τ) (hU : 0 ≤ U)
    (hK0 : ∀ v, 0 < v → 0 ≤ K v) (hKi : IntegrableOn K (Ioi 0) volume)
    (hβ : ∫ v in Ioi 0, K v = β)
    (hQ1 : β * τ - η ≤ ∫ p in T τ, K (p.1 - p.2)) :
    (3 / 2) * (∫ x in (0:ℝ)..τ, h x ^ 2) - 4 * (∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * τ
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in (0:ℝ)..τ, (U - h x))
        + 4 * U ^ 2 * η :=
  lemma4_reduced H hτ hU hQ1 (fun _ ht => inner1_le ht.1 hK0 hKi hβ)
    (fun _ hu => inner2_le hu.2 hK0 hKi hβ)

/-- `Q1 = ∫_{v∈[0,τ]} (τ - v) K(v)`, by two triangle Fubinis and a 1-D shift. -/
theorem Q1_eq {K : ℝ → ℝ} {τ KM : ℝ} (hKm : Measurable K)
    (hKb : ∀ v, 0 ≤ v → v ≤ τ → 0 ≤ K v ∧ K v ≤ KM) :
    ∫ p in T τ, K (p.1 - p.2) = ∫ v in Icc 0 τ, (τ - v) * K v := by
  have hKmp : Measurable (fun p : ℝ × ℝ => K (p.1 - p.2)) :=
    hKm.comp (measurable_fst.sub measurable_snd)
  have i1 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2)) (T τ) volume :=
    integrableOn_T hKmp τ KM (fun p hp => by
      obtain ⟨h1, h2, h3⟩ := hp
      have := hKb (p.1 - p.2) (by linarith) (by linarith)
      rw [abs_of_nonneg this.1]; exact this.2)
  have i2 : IntegrableOn (fun p : ℝ × ℝ => K p.2) (T τ) volume :=
    integrableOn_T (hKm.comp measurable_snd) τ KM (fun p hp => by
      obtain ⟨h1, h2, h3⟩ := hp
      have := hKb p.2 h1 (by linarith)
      show |K p.2| ≤ KM
      rw [abs_of_nonneg this.1]; exact this.2)
  rw [tri_iter i1]
  have hshift : EqOn (fun t => ∫ u in Icc 0 t, K (t - u)) (fun t => ∫ u in Icc 0 t, K u)
      (Icc 0 τ) := by
    intro t ht
    simp only
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht.1, ← intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
  rw [setIntegral_congr_fun measurableSet_Icc hshift]
  have e2 := tri_iter i2
  have e3 := tri_iter_swap i2
  simp only at e2 e3
  rw [← e2, e3]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  simp only
  rw [MeasureTheory.integral_const, smul_eq_mul]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [hv.2])]

/-- **The `Q1` bound** `∫_T K(t-u) ≥ βτ - η`, from `K ≥ 0`, `∫_{(0,∞)} K = β`,
`∫_{(0,∞)} v K(v) = η` (with integrability). -/
theorem Q1_ge {K : ℝ → ℝ} {τ KM β η : ℝ} (hτ : 0 ≤ τ) (hKm : Measurable K)
    (hKb : ∀ v, 0 ≤ v → v ≤ τ → 0 ≤ K v ∧ K v ≤ KM) (hK0 : ∀ v, 0 < v → 0 ≤ K v)
    (hKi : IntegrableOn K (Ioi 0) volume) (hβ : ∫ v in Ioi 0, K v = β)
    (hMi : IntegrableOn (fun v => v * K v) (Ioi 0) volume)
    (hη : ∫ v in Ioi 0, v * K v = η) :
    β * τ - η ≤ ∫ p in T τ, K (p.1 - p.2) := by
  rw [Q1_eq hKm hKb, integral_Icc_eq_integral_Ioc]
  have hfi : IntegrableOn (fun v => (τ - v) * K v) (Ioi 0) volume := by
    have : (fun v => (τ - v) * K v) = fun v => τ * K v - v * K v := by ext v; ring
    rw [this]; exact (hKi.const_mul τ).sub hMi
  have hsplit : ∫ v in Ioi 0, (τ - v) * K v
      = (∫ v in Ioc 0 τ, (τ - v) * K v) + ∫ v in Ioi τ, (τ - v) * K v := by
    rw [← Ioc_union_Ioi_eq_Ioi hτ] at hfi ⊢
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hfi.mono_set subset_union_left) (hfi.mono_set subset_union_right)
  have hneg : ∫ v in Ioi τ, (τ - v) * K v ≤ 0 := by
    apply setIntegral_nonpos measurableSet_Ioi
    intro v hv
    have : 0 ≤ K v := hK0 v (lt_of_le_of_lt hτ hv)
    have : τ - v ≤ 0 := by linarith [show τ < v from hv]
    nlinarith
  have hlin : ∫ v in Ioi 0, (τ - v) * K v = β * τ - η := by
    have : (fun v => (τ - v) * K v) = fun v => τ * K v - v * K v := by ext v; ring
    rw [this, integral_sub (hKi.const_mul τ) hMi, MeasureTheory.integral_const_mul, hβ, hη]
    ring
  linarith

/-- **Lemma 4 at integral level, all kernel inputs discharged** except the 1-D kernel data
(`K ≥ 0`, bounded on `[0,τ]`, mass `β`, first moment `η`). -/
theorem lemma4_integral {K h : ℝ → ℝ} {L U τ KM β η : ℝ} (H : Hyp K h L U τ KM)
    (hτ : 0 ≤ τ) (hU : 0 ≤ U)
    (hK0 : ∀ v, 0 < v → 0 ≤ K v) (hKi : IntegrableOn K (Ioi 0) volume)
    (hβ : ∫ v in Ioi 0, K v = β)
    (hMi : IntegrableOn (fun v => v * K v) (Ioi 0) volume)
    (hη : ∫ v in Ioi 0, v * K v = η) :
    (3 / 2) * (∫ x in (0:ℝ)..τ, h x ^ 2) - 4 * (∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * τ
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in (0:ℝ)..τ, (U - h x))
        + 4 * U ^ 2 * η :=
  lemma4_from_mass H hτ hU hK0 hKi hβ
    (Q1_ge hτ H.hKm (fun v h0 h1 => ⟨H.hK0 v h0 h1, H.hKM v h0 h1⟩) hK0 hKi hβ hMi hη)

end Erdos271.Lemma4

#print axioms Erdos271.Lemma4.tri_iter
#print axioms Erdos271.Lemma4.tri_iter_swap
#print axioms Erdos271.Lemma4.C1_le
#print axioms Erdos271.Lemma4.C2_le
#print axioms Erdos271.Lemma4.lemma4_reduced
#print axioms Erdos271.Lemma4.lemma4_from_mass
#print axioms Erdos271.Lemma4.Q1_eq
#print axioms Erdos271.Lemma4.Q1_ge
#print axioms Erdos271.Lemma4.lemma4_integral
