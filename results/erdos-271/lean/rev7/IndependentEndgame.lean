import Audit.Side
import DefectBudget
import LogEscape
import ZeroAdjoin

open MeasureTheory Set Real Filter
open Erdos271.Side

namespace Erdos271.IndependentEndgame

variable (S : Set ℕ) [DecidablePred (· ∈ S)]

noncomputable def fixedError (s x0 : ℕ) (U : ℝ) : ℝ :=
  (harmonic s : ℝ) +
    (∑ z ∈ (Finset.Ioc s x0).filter (fun z => z ∈ S), (z : ℝ)⁻¹) +
    2 * U / Real.sqrt (x0 : ℝ) +
    (3 / 2) * (∫ x in Set.Ioo 1 (x0 : ℝ), AS S x ^ 2 / x ^ 2) +
    (17 / 2) * U ^ 2

theorem fixed_error_budget (h0 : 0 ∈ S) (s x0 : ℕ) (L U : ℝ)
    (hs0 : s ≤ x0) (hx0 : 0 < x0) (hU : 0 ≤ U)
    (hcov : ∀ z, s < z → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z)
    (henv : ∀ x : ℝ, (x0 : ℝ) ≤ x →
      L * √x ≤ AS S x ∧ AS S x ≤ U * √x) :
    ∀ X : ℕ, x0 ≤ X →
      Erdos271.WeightedCover.Rex (Pfin S X) s X +
        (2 * Erdos271.FinalBudget.alpha * U - (3 / 2) * (U - L)) *
          Erdos271.FinalBudget.deficit (Pfin S X) x0 X U ≤
      (Erdos271.FinalBudget.alpha * U ^ 2 - 1) *
        (Real.log (X : ℝ) - Real.log (x0 : ℝ)) + fixedError S s x0 U := by
  intro X hX
  have h0P : 0 ∈ Pfin S X := by
    simp only [Pfin, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, h0⟩
  have hPX : ∀ p ∈ Pfin S X, p ≤ X := by
    intro p hp
    simp only [Pfin, Finset.mem_filter, Finset.mem_range] at hp
    omega
  have hcovP : ∀ z ∈ Finset.Ioc s X, z ∉ Pfin S X →
      ∃ a ∈ Pfin S X, ∃ b ∈ Pfin S X, a < b ∧ 2 * b - a = z := by
    intro z hz hn
    rw [Finset.mem_Ioc] at hz
    have hnS : z ∉ S := by
      intro hzS
      apply hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzS⟩
    obtain ⟨a, ha, b, hb, hab, heq⟩ := hcov z hz.1 hnS
    refine ⟨a, ?_, b, ?_, hab, heq⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩
  have henvP : ∀ x ∈ Set.Icc (x0 : ℝ) (X : ℝ),
      L * √x ≤ Acount (Erdos271.Glue.Pr (Pfin S X)) x ∧
      Acount (Erdos271.Glue.Pr (Pfin S X)) x ≤ U * √x := by
    intro x hx
    rw [Acount_Pfin S (le_trans (Nat.cast_nonneg _) hx.1) hx.2]
    exact henv x hx.1
  have h := Erdos271.FinalBudget.per_cutoff_budget (Pfin S X) s x0 X L U
    h0P hPX hs0 hx0 hX hU hcovP henvP
  rw [members_indep S hX, I0_indep S (by exact_mod_cast hX)] at h
  exact h

theorem no_small_eventual_envelope (h0 : 0 ∈ S) (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ U : ℝ, U < 1 / √Erdos271.Alpha.α →
      ¬ ∀ᶠ x : ℝ in atTop, AS S x ≤ U * √x := by
  intro U hU hev
  let V : ℝ := max U 1
  have hV0 : 0 ≤ V := le_trans zero_le_one (le_max_right _ _)
  have hVC : V < 1 / √Erdos271.Alpha.α :=
    max_lt hU Erdos271.Side.Cstar_gt_one
  have hevV : ∀ᶠ x : ℝ in atTop, AS S x ≤ V * √x := by
    filter_upwards [hev] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg x))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevV
  let x0 : ℕ := max s (max 1 ⌈max M ((156 + 50 * (s : ℝ)) ^ 2)⌉₊)
  have hs0 : s ≤ x0 := le_max_left _ _
  have h01 : 1 ≤ x0 := (le_max_left _ _).trans (le_max_right _ _)
  have hceil : ⌈max M ((156 + 50 * (s : ℝ)) ^ 2)⌉₊ ≤ x0 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hbase : max M ((156 + 50 * (s : ℝ)) ^ 2) ≤ (x0 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have henv : ∀ x : ℝ, (x0 : ℝ) ≤ x →
      (7 / 5) * √x ≤ AS S x ∧ AS S x ≤ V * √x := by
    intro x hx
    exact ⟨lower_env S s hcov x ((le_max_right _ _).trans (hbase.trans hx)),
      hM x ((le_max_left _ _).trans (hbase.trans hx))⟩
  have hα : 0 < Erdos271.Alpha.α := Erdos271.Alpha.alpha_pos
  have hsα : 0 < √Erdos271.Alpha.α := Real.sqrt_pos.mpr hα
  have hmult : V * √Erdos271.Alpha.α < 1 := (lt_div_iff₀ hsα).mp hVC
  have hmult0 : 0 ≤ V * √Erdos271.Alpha.α := mul_nonneg hV0 hsα.le
  have hsq : (V * √Erdos271.Alpha.α) ^ 2 < 1 := by nlinarith
  rw [mul_pow, Real.sq_sqrt hα.le] at hsq
  have ha : Erdos271.FinalBudget.alpha * V ^ 2 < 1 := by
    change Erdos271.Alpha.α * V ^ 2 < 1
    nlinarith
  obtain ⟨n, hn, hnegative⟩ := Erdos271.Endgame.logarithmic_budget_bundle.1
    (Erdos271.FinalBudget.alpha * V ^ 2) (fixedError S s x0 V)
    (Real.log (x0 : ℝ)) ha x0
  have hbudget := fixed_error_budget S h0 s x0 (7 / 5) V hs0
    (by omega) hV0 hcov henv n hn
  have hR : 0 ≤ Erdos271.WeightedCover.Rex (Pfin S n) s n :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
  have hx0p : (0 : ℝ) < x0 := by exact_mod_cast (show 0 < x0 by omega)
  have hxn : (x0 : ℝ) ≤ n := by exact_mod_cast hn
  have henvP : ∀ x ∈ Set.Icc (x0 : ℝ) (n : ℝ),
      (7 / 5) * √x ≤ Acount (Erdos271.Glue.Pr (Pfin S n)) x ∧
      Acount (Erdos271.Glue.Pr (Pfin S n)) x ≤ V * √x := by
    intro x hx
    rw [Acount_Pfin S (le_trans (Nat.cast_nonneg _) hx.1) hx.2]
    exact henv x hx.1
  have hD : 0 ≤ Erdos271.FinalBudget.deficit (Pfin S n) x0 n V := by
    apply D_nonneg (Real.log_le_log hx0p hxn)
    intro t ht
    exact (Erdos271.Glue.hfun_env (Erdos271.Glue.Pr (Pfin S n))
      hx0p hxn henvP t ht).2
  have hk : 0 ≤ 2 * Erdos271.FinalBudget.alpha * V - (3 / 2) * (V - 7 / 5) :=
    (Erdos271.Side.kappa_pos hV0 (hVC.trans Erdos271.Alpha.Cstar_lt)).le
  have hnonnegative := add_nonneg hR (mul_nonneg hk hD)
  linarith

theorem AS_insert_zero (x : ℝ) : AS (insert 0 S) x = AS S x := by
  classical
  unfold AS
  congr 2
  apply Finset.filter_congr
  intro n _
  change ((n = 0 ∨ n ∈ S) ∧ 0 < n) ↔ (n ∈ S ∧ 0 < n)
  constructor
  · rintro ⟨h, hp⟩
    rcases h with h | h
    · omega
    · exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩
    exact ⟨Or.inr h, hp⟩

theorem no_small_eventual_envelope_any (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ U : ℝ, U < 1 / √Erdos271.Alpha.α →
      ¬ ∀ᶠ x : ℝ in atTop, AS S x ≤ U * √x := by
  classical
  have hcov0 := Erdos271.Endgame.zero_adjoining_bundle.1 S s hcov
  intro U hU hev
  apply no_small_eventual_envelope (insert 0 S) (Set.mem_insert 0 S) s hcov0 U hU
  filter_upwards [hev] with x hx
  rw [AS_insert_zero S x]
  exact hx

theorem arbitrarily_large_witnesses (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ U : ℝ, U < 1 / √Erdos271.Alpha.α →
      ∀ R : ℝ, ∃ x : ℝ, R ≤ x ∧ U * √x < AS S x := by
  intro U hU R
  by_contra h
  push_neg at h
  apply no_small_eventual_envelope_any S s hcov U hU
  exact eventually_atTop.mpr ⟨R, fun x hx => h x hx⟩

end Erdos271.IndependentEndgame
