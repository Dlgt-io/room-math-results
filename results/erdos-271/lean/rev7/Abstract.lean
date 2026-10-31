import Statement
import Audit.General

-- Preserve the legacy analytic modules; this bridge therefore uses their import mode.

/-!
# Bridges from the preserved proof to the paper abstract
-/

open Filter Real Finset
attribute [local instance] Classical.propDecidable

namespace Erdos271.Abstract

theorem F_nonneg (S : Set ℕ) (x : ℝ) : 0 ≤ F S x := by
  classical
  unfold F
  split <;> positivity

/-- The positive and inclusive counts differ only at zero. -/
theorem F_eq_AS_add_zero (S : Set ℕ) (x : ℝ) (hx : 0 ≤ x) :
    F S x = Side.AS S x + if 0 ∈ S then 1 else 0 := by
  classical
  unfold F
  rw [ite_eq_right (not_lt_of_ge hx)]
  let T := (range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S)
  have hpos : (range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n) = T.erase 0 := by
    ext n
    simp only [T, mem_filter, mem_range, mem_erase, Nat.pos_iff_ne_zero]
    tauto
  have hzero : 0 ∈ T ↔ 0 ∈ S := by simp [T]
  change (T.card : ℝ) = Side.AS S x + if 0 ∈ S then 1 else 0
  unfold Side.AS
  rw [hpos]
  by_cases hz : 0 ∈ S
  · rw [ite_eq_left hz]
    exact_mod_cast (card_erase_add_one (hzero.mpr hz)).symm
  · rw [ite_eq_right hz, erase_eq_of_notMem (fun h => hz (hzero.mp h)), add_zero]

theorem AS_le_F (S : Set ℕ) (x : ℝ) (hx : 0 ≤ x) : Side.AS S x ≤ F S x := by
  classical
  rw [F_eq_AS_add_zero S x hx]
  split <;> linarith

/-- The constant in the abstract is exactly the constant in the analytic proof. -/
theorem constant_eq :
    1 / √(Real.log (1 + √2) / (2 * √2)) =
      √(2 * √2 / Real.log (1 + √2)) := by
  rw [one_div, ← Real.sqrt_inv, inv_div]

theorem inclusive_limsup (S : Set ℕ) (hS : WeaklyAP3Covering S) :
    ENNReal.ofReal (√(2 * √2 / Real.log (1 + √2))) ≤
      limsup (fun x : ℝ => ENNReal.ofReal (F S x / √x)) atTop := by
  classical
  obtain ⟨s, hcov⟩ := hS
  have hcov' : ∀ z, s < z → z ∉ S →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z := by
    intro z hz hzS
    obtain ⟨a, ha, b, hb, hab, _, he⟩ := hcov z hz hzS
    exact ⟨a, ha, b, hb, hab, he.symm⟩
  refine Filter.le_limsup_of_le (hf := by isBoundedDefault) ?_
  intro b hb
  by_contra hn
  have hlt : b < ENNReal.ofReal (√(2 * √2 / Real.log (1 + √2))) := lt_of_not_ge hn
  have hbtop : b ≠ ⊤ := ne_top_of_lt hlt
  have hCnonneg : 0 ≤ √(2 * √2 / Real.log (1 + √2)) := Real.sqrt_nonneg _
  have hbU : b.toReal < √(2 * √2 / Real.log (1 + √2)) := by
    have h := (ENNReal.toReal_lt_toReal hbtop ENNReal.ofReal_ne_top).mpr hlt
    simpa only [ENNReal.toReal_ofReal hCnonneg] using h
  apply Final.erdos271_limsup_any S s hcov' b.toReal
    (by simpa only [constant_eq] using hbU)
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hquot : F S x / √x ≤ b.toReal := by
    have h := ENNReal.toReal_mono hbtop hx
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (F_nonneg S x) (Real.sqrt_nonneg x))] using h
  exact (AS_le_F S x hx0.le).trans ((div_le_iff₀ (Real.sqrt_pos.mpr hx0)).mp hquot)

end Erdos271.Abstract
