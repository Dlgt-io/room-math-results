import Audit.Glue4
import Audit.KMChecked
import Audit.Moment0

/-!
# Lemma 4 on a window, with the concrete kernel data discharged

Uses ChatGPT's `kernel_formula` (mass) and `FirstMoment_checked` (first moment, `0 ≤ η ≤ 2`),
both stated for any `K` with the kernel's defining equation.
-/

open MeasureTheory Set Real

namespace Erdos271.Lemma4

theorem Kker_spec (v : ℝ) : Kker v = Real.exp (-3 * v / 2) / (2 - Real.exp (-v)) ^ 3 := by
  unfold Kker; congr 2; ring

/-- **Lemma 4, concrete kernel, window `[t0, T]`, no kernel hypotheses.**
With `β = 3/8 - log(1+√2)/(8√2)` and `η = ∫_{(0,∞)} v Kker(v) ∈ [0, 2]`. -/
theorem lemma4_concrete {h : ℝ → ℝ} {L U t0 T : ℝ} (hm : Measurable h) (hT : t0 ≤ T)
    (hU : 0 ≤ U) (hb : ∀ x ∈ Icc t0 T, L ≤ h x ∧ h x ≤ U) :
    let β : ℝ := 3 / 8 - Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2)
    let η : ℝ := ∫ v in Ioi 0, v * Kker v
    0 ≤ η ∧ η ≤ 2 ∧
    (3 / 2) * (∫ x in t0..T, h x ^ 2)
      - 4 * (∫ t in Ioo t0 T, h t * ∫ u in Ioo t0 t, Kker (t - u) * h u)
      ≤ (3 / 2 - 4 * β) * U ^ 2 * (T - t0)
        - (2 * (3 / 2 - 4 * β) * U - (3 / 2) * (U - L)) * (∫ x in t0..T, (U - h x))
        + 4 * U ^ 2 * η := by
  intro β η
  obtain ⟨hKi, hβ⟩ := Erdos271.KernelMass.kernel_formula Kker Kker_spec
  obtain ⟨hMi, h0, h2⟩ := Erdos271.RoundTwo.FirstMoment_checked Kker (fun v => v * Kker v)
    Kker_spec (fun v => rfl)
  exact ⟨h0, h2, lemma4_window hm hT hU hb hKi hβ hMi rfl⟩

end Erdos271.Lemma4

#print axioms Erdos271.Lemma4.lemma4_concrete
