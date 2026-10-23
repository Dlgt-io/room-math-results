import Audit.TriFubini
import Audit.LogSub

/-!
# Lemma 4 glue: concrete kernel, triangle ↔ iterated form, window shift

* `Kker_measurable`, `Kker_bounds`: the concrete kernel of `LogSub.lean` is measurable and
  `0 ≤ Kker ≤ 1` on `[0, ∞)`.
* `Q_eq_iter`: the closed-triangle form `Q_τ` equals the iterated open-interval form used in
  `J_logsub` (boundaries are null).
* `shift_Ioo`, `iter_shift`: translating the window `[t0, T]` to `[0, T - t0]`.
* `lemma4_window`: Lemma 4 for the concrete kernel on a window `[t0, T]`, in the iterated
  form of `J_logsub`.
-/

open MeasureTheory Set Real

namespace Erdos271.Lemma4

theorem Kker_measurable : Measurable Kker := by
  unfold Kker; fun_prop

theorem Kker_bounds {v : ℝ} (hv : 0 ≤ v) : 0 ≤ Kker v ∧ Kker v ≤ 1 := by
  have h1 : exp (-v) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hd : 1 ≤ (2 - exp (-v)) ^ 3 := one_le_pow₀ (by linarith)
  have he : exp (-(3 * v / 2)) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  unfold Kker
  refine ⟨div_nonneg (exp_pos _).le (by positivity), ?_⟩
  calc exp (-(3 * v / 2)) / (2 - exp (-v)) ^ 3 ≤ exp (-(3 * v / 2)) :=
        div_le_self (exp_pos _).le hd
    _ ≤ 1 := he

/-- **Triangle form = iterated open-interval form.** -/
theorem Q_eq_iter {K h : ℝ → ℝ} {L U τ KM : ℝ} (H : Hyp K h L U τ KM) :
    ∫ p in T τ, K (p.1 - p.2) * h p.1 * h p.2
      = ∫ t in Ioo 0 τ, h t * ∫ u in Ioo 0 t, K (t - u) * h u := by
  have hKmp : Measurable (fun p : ℝ × ℝ => K (p.1 - p.2)) :=
    H.hKm.comp (measurable_fst.sub measurable_snd)
  set B := |L| + |U|
  have hB : ∀ x ∈ Icc 0 τ, |h x| ≤ B := fun x hx =>
    abs_le_of_bounds (H.hb x hx).1 (H.hb x hx).2
  have i3 : IntegrableOn (fun p : ℝ × ℝ => K (p.1 - p.2) * h p.1 * h p.2) (T τ) volume :=
    integrableOn_T (f := fun p : ℝ × ℝ => K (p.1 - p.2) * h p.1 * h p.2)
      ((hKmp.mul (H.hm.comp measurable_fst)).mul (H.hm.comp measurable_snd)) τ (KM * B * B)
      (fun p hp => by
        obtain ⟨k0, k1, ht, hu⟩ := kdiff_bounds H hp
        show |K (p.1 - p.2) * h p.1 * h p.2| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg k0]
        have hb1 := hB _ ht
        have hb2 := hB _ hu
        have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hb1
        exact mul_le_mul (mul_le_mul k1 hb1 (abs_nonneg _) (le_trans k0 k1)) hb2
          (abs_nonneg _) (mul_nonneg (le_trans k0 k1) hB0))
  rw [tri_iter i3, integral_Icc_eq_integral_Ioo]
  congr 1; ext t
  rw [integral_Icc_eq_integral_Ioo, ← MeasureTheory.integral_const_mul]
  congr 1; ext u; ring

/-- One-dimensional window shift. -/
theorem shift_Ioo (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Ioo a b, f x = ∫ x in Ioo 0 (b - a), f (x + a) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_add_right]
  simp

/-- **Iterated form on `[t0, T]` = iterated form of the shifted function on `[0, T - t0]`.** -/
theorem iter_shift (K h : ℝ → ℝ) {t0 T : ℝ} (hT : t0 ≤ T) :
    ∫ t in Ioo t0 T, h t * ∫ u in Ioo t0 t, K (t - u) * h u
      = ∫ t in Ioo 0 (T - t0), h (t + t0) * ∫ u in Ioo 0 t, K (t - u) * h (u + t0) := by
  rw [shift_Ioo _ hT]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  simp only
  rw [shift_Ioo _ (by linarith [ht.1] : t0 ≤ t + t0)]
  congr 1
  rw [show t + t0 - t0 = t by ring]
  congr 1; ext u
  rw [show t + t0 - (u + t0) = t - u by ring]

/-- **Lemma 4 on a window `[t0, T]`, concrete kernel, iterated form of `J_logsub`.** -/
theorem lemma4_window {h : ℝ → ℝ} {L U t0 T β η : ℝ} (hm : Measurable h) (hT : t0 ≤ T)
    (hU : 0 ≤ U) (hb : ∀ x ∈ Icc t0 T, L ≤ h x ∧ h x ≤ U)
    (hKi : IntegrableOn Kker (Ioi 0) volume) (hβ : ∫ v in Ioi 0, Kker v = β)
    (hMi : IntegrableOn (fun v => v * Kker v) (Ioi 0) volume)
    (hη : ∫ v in Ioi 0, v * Kker v = η) :
    (3 / 2) * (∫ x in t0..T, h x ^ 2)
      - 4 * (∫ t in Ioo t0 T, h t * ∫ u in Ioo t0 t, Kker (t - u) * h u)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * (T - t0)
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in t0..T, (U - h x))
        + 4 * U ^ 2 * η := by
  set g : ℝ → ℝ := fun t => h (t + t0) with hg
  have Hg : Hyp Kker g L U (T - t0) 1 :=
    { hKm := Kker_measurable
      hm := hm.comp (measurable_id.add_const t0)
      hK0 := fun v hv _ => (Kker_bounds hv).1
      hKM := fun v hv _ => (Kker_bounds hv).2
      hb := fun x hx => hb (x + t0) ⟨by linarith [hx.1], by linarith [hx.2]⟩ }
  have main := lemma4_integral Hg (by linarith) hU (fun v hv => (Kker_bounds hv.le).1)
    hKi hβ hMi hη
  rw [Q_eq_iter Hg] at main
  have e1 : ∫ x in (0:ℝ)..(T - t0), g x ^ 2 = ∫ x in t0..T, h x ^ 2 := by
    simp only [hg]
    rw [intervalIntegral.integral_comp_add_right (fun x => h x ^ 2)]; simp
  have e2 : ∫ x in (0:ℝ)..(T - t0), (U - g x) = ∫ x in t0..T, (U - h x) := by
    simp only [hg]
    rw [intervalIntegral.integral_comp_add_right (fun x => U - h x)]; simp
  rw [e1, e2] at main
  rw [iter_shift Kker h hT]
  exact main

end Erdos271.Lemma4

#print axioms Erdos271.Lemma4.Kker_measurable
#print axioms Erdos271.Lemma4.Kker_bounds
#print axioms Erdos271.Lemma4.Q_eq_iter
#print axioms Erdos271.Lemma4.shift_Ioo
#print axioms Erdos271.Lemma4.iter_shift
#print axioms Erdos271.Lemma4.lemma4_window
