import Audit.Bridge

open MeasureTheory Set Real
open Erdos271.FiniteIntegrals

namespace Erdos271.FinalBudget

noncomputable def alpha : ℝ :=
  Real.log (1 + Real.sqrt 2) / (2 * Real.sqrt 2)

noncomputable def deficit (P : Finset ℕ) (x0 X : ℕ) (U : ℝ) : ℝ :=
  ∫ t in (Real.log (x0 : ℝ))..(Real.log (X : ℝ)),
    (U - hfun (Acount (Erdos271.Glue.Pr P)) t)

/-- A finite-cutoff defect budget from the actual covering, integral identity and
logarithmic-window theorem. No integral estimate or defect budget is a premise.
The initial terms are still written using P; stabilizing them for prefixes of an
infinite S is a separate subsequent lemma. -/
theorem per_cutoff_budget (P : Finset ℕ) (s x0 X : ℕ) (L U : ℝ)
    (h0 : 0 ∈ P) (hPX : ∀ p ∈ P, p ≤ X)
    (hsx : s ≤ x0) (hx0 : 0 < x0) (hxX : x0 ≤ X) (hU : 0 ≤ U)
    (hcov : ∀ z ∈ Finset.Ioc s X, z ∉ P →
      ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z)
    (henv : ∀ x ∈ Set.Icc (x0 : ℝ) (X : ℝ),
      L * Real.sqrt x ≤ Acount (Erdos271.Glue.Pr P) x ∧
      Acount (Erdos271.Glue.Pr P) x ≤ U * Real.sqrt x) :
    Erdos271.WeightedCover.Rex P s X +
      (2 * alpha * U - (3 / 2) * (U - L)) * deficit P x0 X U ≤
    (alpha * U ^ 2 - 1) * (Real.log (X : ℝ) - Real.log (x0 : ℝ)) +
      ((harmonic s : ℝ) +
       (∑ z ∈ (Finset.Ioc s x0).filter (fun z => z ∈ P), (z : ℝ)⁻¹) +
       2 * U / Real.sqrt (x0 : ℝ) +
       (3 / 2) * (∫ x in Set.Ioo 1 (x0 : ℝ),
         Acount (Erdos271.Glue.Pr P) x ^ 2 / x ^ 2) +
       (17 / 2) * U ^ 2) := by
  classical
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  have hx0one : (1 : ℝ) ≤ x0 := by exact_mod_cast hx0
  have hxXr : (x0 : ℝ) ≤ X := by exact_mod_cast hxX
  have hXp : (0 : ℝ) < X := lt_of_lt_of_le hx0r hxXr
  have hPr := Erdos271.Glue.Pr_mem P hPX
  have hfin := finite_weighted_integral_identity
    (Erdos271.Glue.Pr P) (X : ℝ) hXp
    (fun p hp => ⟨lt_of_lt_of_le zero_lt_one (hPr p hp).1, (hPr p hp).2⟩)
  have hlow := Erdos271.MemberTail.lemma2_full P U s x0 X hsx hxX hx0 hU hcov
    (Erdos271.Glue.env_nat P henv)
  rw [Erdos271.Glue.W_eq_weightedPairs P h0] at hlow
  have hwin := Erdos271.Glue.log_window_bound (Erdos271.Glue.Pr P)
    (fun p hp => (hPr p hp).1) hx0one hxXr hU henv
  dsimp only at hwin
  obtain ⟨hη0, hη2, hupper⟩ := hwin
  have ha : (3 / 2 : ℝ) - 4 *
      (3 / 8 - Real.log (1 + Real.sqrt 2) / (8 * Real.sqrt 2)) = alpha := by
    unfold alpha
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num
    ring
  rw [ha] at hupper
  change (3 / 2 : ℝ) * squareIntegral (Erdos271.Glue.Pr P) (X : ℝ) -
      4 * doubleIntegral (Erdos271.Glue.Pr P) (X : ℝ) ≤
    (3 / 2 : ℝ) * (∫ x in Set.Ioo 1 (x0 : ℝ),
      Acount (Erdos271.Glue.Pr P) x ^ 2 / x ^ 2) +
    alpha * U ^ 2 * (Real.log (X : ℝ) - Real.log (x0 : ℝ)) -
    (2 * alpha * U - (3 / 2) * (U - L)) * deficit P x0 X U +
    4 * U ^ 2 * (∫ v in Set.Ioi (0 : ℝ), v * Kker v) at hupper
  have hcard : ((Erdos271.Glue.Pr P).card : ℝ) ≤ U * Real.sqrt (X : ℝ) := by
    rw [Erdos271.Glue.card_Pr P hPX, ← Erdos271.Glue.Acount_Pr]
    exact (henv (X : ℝ) ⟨hxXr, le_rfl⟩).2
  have hcard0 : 0 ≤ ((Erdos271.Glue.Pr P).card : ℝ) := Nat.cast_nonneg _
  have hsq := pow_le_pow_left₀ hcard0 hcard 2
  rw [mul_pow, Real.sq_sqrt hXp.le] at hsq
  have hE : boundaryTerm (Erdos271.Glue.Pr P) (X : ℝ) ≤ U ^ 2 / 2 := by
    apply le_trans hfin.2.2.2.2
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (X : ℝ))).mpr
    nlinarith [hsq]
  have hmoment := mul_le_mul_of_nonneg_left hη2
    (by positivity : (0 : ℝ) ≤ 4 * U ^ 2)
  have hlogX := Real.log_le_log hXp (show (X : ℝ) ≤ (X : ℝ) + 1 by linarith)
  have hlog0 := Real.log_nonneg hx0one
  have hw := hfin.2.2.1
  linarith

end Erdos271.FinalBudget
