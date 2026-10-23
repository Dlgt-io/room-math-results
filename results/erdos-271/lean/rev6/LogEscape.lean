import Mathlib
namespace Erdos271.Endgame

theorem logarithmic_budget_bundle :
(∀ a : Real, ∀ C : Real, ∀ t0 : Real, a < 1 → ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ (a - 1) * (Real.log (n : Real) - t0) + C < 0) ∧ (∀ a : Real, ∀ k : Real, ∀ C : Real, ∀ t0 : Real, ∀ R : Nat → Real, ∀ D : Nat → Real, ∀ N : Nat, 0 ≤ k → (∀ n : Nat, N ≤ n → 0 ≤ R n) → (∀ n : Nat, N ≤ n → 0 ≤ D n) → (∀ n : Nat, N ≤ n → R n + k * D n ≤ (a - 1) * (Real.log (n : Real) - t0) + C) → 1 ≤ a) :=
by
  have escape : ∀ a C t0 : Real, a < 1 → ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧ (a - 1) * (Real.log (n : Real) - t0) + C < 0 := by
    intro a C t0 ha N
    have hd : 0 < 1 - a := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt
      (max (N : Real) (Real.exp (t0 + (|C| + 1) / (1 - a))))
    have hnN : (N : Real) < (n : Real) :=
      lt_of_le_of_lt (le_max_left _ _) hn
    have hne : Real.exp (t0 + (|C| + 1) / (1 - a)) < (n : Real) :=
      lt_of_le_of_lt (le_max_right _ _) hn
    have hlog : t0 + (|C| + 1) / (1 - a) < Real.log (n : Real) := by
      have h := Real.log_lt_log (Real.exp_pos _) hne
      simpa only [Real.log_exp] using h
    have hdiv : ((|C| + 1) / (1 - a)) * (1 - a) = |C| + 1 :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    have hprod := mul_lt_mul_of_pos_right
      (show (|C| + 1) / (1 - a) < Real.log (n : Real) - t0 by linarith) hd
    refine ⟨n, ?_, ?_⟩
    · exact_mod_cast hnN.le
    · nlinarith [le_abs_self C]
  refine ⟨escape, ?_⟩
  intro a k C t0 R D N hk hR hD hbudget
  by_contra h
  have ha : a < 1 := lt_of_not_ge h
  obtain ⟨n, hn, hneg⟩ := escape a C t0 ha N
  have hleft : 0 ≤ R n + k * D n :=
    add_nonneg (hR n hn) (mul_nonneg hk (hD n hn))
  have hb := hbudget n hn
  linarith

end Erdos271.Endgame
