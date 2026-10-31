import Audit.Side

/-!
# End-to-end statement, with (6.1) isolated as a named hypothesis

`erdos271_limsup_of`: for a weak AP3-covering `S ⊆ ℕ` (beyond `s`), no `U < C_* = 1/√α` is an
eventual upper envelope for `AS S x / √x`, **provided** the per-`X` defect budget (6.1)
holds in the form `Budget61`. Everything else (Lemma 1 lower envelope, `U < 9/5`, `C_* > 1`,
`αU² < 1`, and the limit `log X → ∞`) is proved here.

The single remaining obligation is `H61` below: from the two-sided envelope
`(7/5)√x ≤ A(x) ≤ U√x` (for `x ≥ x0`, `0 ≤ U < C_*`), deduce
`log X ≤ α U² log X + C` for all natural `X ≥ x0'`. All its ingredients are compiled
(`lemma2_full`, `W_eq_weightedPairs`, `finite_weighted_integral_identity`,
`log_window_bound`, `I0_indep`, `members_indep`, `D_nonneg`, `E_le`, `beta_eq`, `kappa_pos`).
-/

open MeasureTheory Set Real Filter
open Erdos271.Alpha Erdos271.Side

namespace Erdos271.Final

variable (S : Set ℕ) [DecidablePred (· ∈ S)]

/-- (6.1) in the form used by the limit step. -/
def Budget61 (U : ℝ) : Prop :=
  ∃ C : ℝ, ∃ x0 : ℕ, ∀ X : ℕ, x0 ≤ X → Real.log X ≤ α * U ^ 2 * Real.log X + C

/-- The named remaining obligation: the per-`X` defect budget (6.1). -/
def H61 : Prop :=
  ∀ U : ℝ, 0 ≤ U → U < 1 / √α →
    (∃ x0 : ℕ, 1 ≤ x0 ∧ ∀ x : ℝ, (x0 : ℝ) ≤ x → (7 / 5) * √x ≤ AS S x ∧ AS S x ≤ U * √x) →
    Budget61 U

/-- **Limit step.** `αU² < 1` and the budget are incompatible. -/
theorem limit_of_budget {U : ℝ} (hc : α * U ^ 2 < 1) (hB : Budget61 U) : False := by
  obtain ⟨C, x0, hX⟩ := hB
  set c := α * U ^ 2
  have hpos : 0 < 1 - c := by linarith
  set X : ℕ := max x0 ⌈Real.exp (C / (1 - c) + 1)⌉₊
  have h1 := hX X (le_max_left _ _)
  have hXe : Real.exp (C / (1 - c) + 1) ≤ X := le_trans (Nat.le_ceil _)
    (by exact_mod_cast le_max_right _ _)
  have hlog : C / (1 - c) + 1 ≤ Real.log X := by
    rw [← Real.log_exp (C / (1 - c) + 1)]
    exact Real.log_le_log (Real.exp_pos _) hXe
  have : (1 - c) * (C / (1 - c) + 1) ≤ (1 - c) * Real.log X :=
    mul_le_mul_of_nonneg_left hlog hpos.le
  have e : (1 - c) * (C / (1 - c) + 1) = C + (1 - c) := by field_simp
  nlinarith

theorem sq_lt_of_lt_Cstar {V : ℝ} (hV0 : 0 ≤ V) (hV : V < 1 / √α) : α * V ^ 2 < 1 := by
  have ha := alpha_pos
  have hs := Real.sqrt_pos.mpr ha
  have h1 : V * √α < 1 := by rwa [lt_div_iff₀ hs] at hV
  have h2 : (V * √α) ^ 2 < 1 := by
    have : 0 ≤ V * √α := mul_nonneg hV0 hs.le
    nlinarith
  rwa [mul_pow, Real.sq_sqrt ha.le, mul_comm] at h2

/-- **End-to-end theorem, conditional on (6.1) only.** -/
theorem erdos271_limsup_of (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z)
    (h61 : H61 S) :
    ∀ U : ℝ, U < 1 / √α → ¬ ∀ᶠ x : ℝ in atTop, AS S x ≤ U * √x := by
  intro U hU hev
  set V := max U 1 with hVdef
  have hV0 : 0 ≤ V := le_trans zero_le_one (le_max_right _ _)
  have hV : V < 1 / √α := max_lt hU Cstar_gt_one
  have hev' : ∀ᶠ x : ℝ in atTop, AS S x ≤ V * √x := by
    filter_upwards [hev] with x hx
    exact le_trans hx (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev'
  set x0 : ℕ := ⌈max (max M ((156 + 50 * (s : ℝ)) ^ 2)) 1⌉₊
  have hx0 : max (max M ((156 + 50 * (s : ℝ)) ^ 2)) 1 ≤ x0 := Nat.le_ceil _
  have hx01 : 1 ≤ x0 := by
    have : (1 : ℝ) ≤ x0 := le_trans (le_max_right _ _) hx0
    exact_mod_cast this
  refine limit_of_budget (sq_lt_of_lt_Cstar hV0 hV) (h61 V hV0 hV ⟨x0, hx01, fun x hx => ?_⟩)
  have hxM : M ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hx0 hx)
  have hxs : (156 + 50 * (s : ℝ)) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hx0 hx)
  exact ⟨lower_env S s hcov x hxs, hM x hxM⟩

/-- Limsup form (bounded case; the unbounded case is trivially `≥ C_*`). -/
theorem erdos271_limsup_ge_of (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z)
    (h61 : H61 S) (hb : IsBoundedUnder (· ≤ ·) atTop (fun x => AS S x / √x)) :
    1 / √α ≤ limsup (fun x => AS S x / √x) atTop := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, h1, h2⟩ := exists_between hlt
  exact erdos271_limsup_of S s hcov h61 U h2 (env_of_limsup S hb h1)

end Erdos271.Final
