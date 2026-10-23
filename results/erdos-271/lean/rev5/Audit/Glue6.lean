import Audit.Glue5
import WeightedIdentity

/-!
# `log_window_bound`: Lemma 4 for the counting function, in terms of the finite identity

For a finite `P ⊂ [1, ∞)` and `1 ≤ x0 ≤ X` with the envelope `L√x ≤ A(x) ≤ U√x` on
`[x0, X]` (`A = Acount P`), the quantity `(3/2) I(X) - 4 J(X)` of ChatGPT's
`finite_weighted_integral_identity` (`squareIntegral`, `doubleIntegral`) is bounded by
the initial part `(3/2) I(x0)` plus the Lemma 4 bound on the window `[log x0, log X]`.
-/

open MeasureTheory Set Real
open Erdos271.FiniteIntegrals

namespace Erdos271.Glue

theorem positiveCount_eq (P : Finset ℝ) : positiveCount P = Acount P := rfl

/-- `squareIntegral` as a set integral over `(1, X)`. -/
theorem squareIntegral_eq (P : Finset ℝ) (hP : ∀ p ∈ P, 1 ≤ p) {X : ℝ} (hX : 0 ≤ X) :
    squareIntegral P X = ∫ x in Ioo 1 X, Acount P x ^ 2 / x ^ 2 := by
  unfold squareIntegral squareIntegrand
  rw [intervalIntegral.integral_of_le hX, integral_Ioc_eq_integral_Ioo, positiveCount_eq]
  exact I_range P hP X

/-- `doubleIntegral` as the iterated set integral over `(1, X)`. -/
theorem doubleIntegral_eq (P : Finset ℝ) (hP : ∀ p ∈ P, 1 ≤ p) {X : ℝ} (hX : 0 ≤ X) :
    doubleIntegral P X
      = ∫ x in Ioo 1 X, Acount P x * ∫ u in Ioo 1 x, Acount P u / (2 * x - u) ^ 3 := by
  unfold doubleIntegral
  rw [intervalIntegral.integral_of_le hX, integral_Ioc_eq_integral_Ioo, ← J_range P hP X]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  unfold doubleIntegrand
  rw [intervalIntegral.integral_of_le ht.1.le, integral_Ioc_eq_integral_Ioo, positiveCount_eq,
    ← MeasureTheory.integral_const_mul]
  congr 1; funext u; ring

theorem I_log (P : Finset ℝ) {X : ℝ} (hX : 0 < X) :
    ∫ x in Ioo 1 X, Acount P x ^ 2 / x ^ 2 = ∫ t in Ioo 0 (log X), hfun (Acount P) t ^ 2 := by
  have := I_logsub (Acount P) (log X)
  rwa [exp_log hX] at this

theorem J_log (P : Finset ℝ) {X : ℝ} (hX : 0 < X) :
    ∫ x in Ioo 1 X, Acount P x * ∫ u in Ioo 1 x, Acount P u / (2 * x - u) ^ 3
      = ∫ τ in Ioo 0 (log X), hfun (Acount P) τ
          * ∫ σ in Ioo 0 τ, Kker (τ - σ) * hfun (Acount P) σ := by
  have := J_logsub (Acount P) (log X)
  rwa [exp_log hX] at this

/-- Splitting `∫_0^T h²` at `t0`. -/
theorem hsq_split (P : Finset ℝ) {t0 T : ℝ} (h0 : 0 ≤ t0) (hT : t0 ≤ T) :
    ∫ t in Ioo 0 T, hfun (Acount P) t ^ 2
      = (∫ t in Ioo 0 t0, hfun (Acount P) t ^ 2) + ∫ t in t0..T, hfun (Acount P) t ^ 2 := by
  have hi : IntervalIntegrable (fun t => hfun (Acount P) t ^ 2) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact h_sq_integrable P T
  have h1 : IntervalIntegrable (fun t => hfun (Acount P) t ^ 2) volume 0 t0 :=
    hi.mono_set (by rw [uIcc_of_le h0, uIcc_of_le (by linarith)]; exact Icc_subset_Icc le_rfl hT)
  have h2 : IntervalIntegrable (fun t => hfun (Acount P) t ^ 2) volume t0 T :=
    hi.mono_set (by rw [uIcc_of_le hT, uIcc_of_le (by linarith)]; exact Icc_subset_Icc h0 le_rfl)
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le h0,
    intervalIntegral.integral_add_adjacent_intervals h1 h2]

/-- **`log_window_bound`.** -/
theorem log_window_bound (P : Finset ℝ) {L U x0 X : ℝ} (hP : ∀ p ∈ P, 1 ≤ p)
    (hx0 : 1 ≤ x0) (hxX : x0 ≤ X) (hU : 0 ≤ U)
    (henv : ∀ x ∈ Icc x0 X, L * √x ≤ Acount P x ∧ Acount P x ≤ U * √x) :
    let β : ℝ := 3 / 8 - Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2)
    let η : ℝ := ∫ v in Ioi 0, v * Kker v
    0 ≤ η ∧ η ≤ 2 ∧
    (3 / 2) * squareIntegral P X - 4 * doubleIntegral P X
      ≤ (3 / 2) * (∫ x in Ioo 1 x0, Acount P x ^ 2 / x ^ 2)
        + (3 / 2 - 4 * β) * U ^ 2 * (log X - log x0)
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L))
            * (∫ t in (log x0)..(log X), (U - hfun (Acount P) t))
        + 4 * U ^ 2 * η := by
  intro β η
  have hx0p : 0 < x0 := by linarith
  have hXp : 0 < X := by linarith
  have ht0 : 0 ≤ log x0 := log_nonneg hx0
  have hT : log x0 ≤ log X := log_le_log hx0p hxX
  have L4 := Erdos271.Lemma4.lemma4_concrete (hfun_meas P) hT hU (hfun_env P hx0p hxX henv)
  simp only at L4
  obtain ⟨hη0, hη2, hmain⟩ := L4
  refine ⟨hη0, hη2, ?_⟩
  have hD := J_drop (hfun_meas P) (B := (P.card : ℝ)) (T := log X) ht0
    (fun x hx _ => ⟨hfun_nonneg P x, hfun_le P hx⟩)
  rw [squareIntegral_eq P hP hXp.le, doubleIntegral_eq P hP hXp.le, I_log P hXp, J_log P hXp,
    I_log P hx0p, hsq_split P ht0 hT]
  simp only [β, η]
  linarith [hD, hmain]

end Erdos271.Glue
