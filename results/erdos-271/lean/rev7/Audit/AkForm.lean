import Audit.Final61

/-!
# The `a_k` form: `liminf a_k / k² ≤ α`

For `S` as in `erdos271_limsup`, `S` is infinite (by Lemma 1) and, with `a_k = Nat.nth S k`
(`a_0 = 0`), no `c > α` satisfies `c k² ≤ a_k` eventually.
-/

open Real Filter Finset
open Erdos271.Alpha Erdos271.Side

namespace Erdos271.Final

variable (S : Set ℕ) [DecidablePred (· ∈ S)]

/-- `count S (⌊x⌋+1) = AS S x + 1` when `0 ∈ S`. -/
theorem count_eq (h0 : 0 ∈ S) (x : ℝ) :
    Nat.count (· ∈ S) (⌊x⌋₊ + 1)
      = ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card + 1 := by
  rw [Nat.count_eq_card_filter_range,
    ← Finset.card_filter_add_card_filter_not (s := (range (⌊x⌋₊ + 1)).filter (· ∈ S))
      (p := fun n => 0 < n), Finset.filter_filter, Finset.filter_filter]
  congr 1
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨_, h⟩; omega
  · rintro rfl; simp [h0]

theorem infinite_of_cover (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) : S.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  set x : ℝ := max ((156 + 50 * (s : ℝ)) ^ 2) (((N : ℝ) + 1) ^ 2)
  have hx := lower_env S s hcov x (le_max_left _ _)
  have hAS : AS S x ≤ N := by
    unfold AS
    have : ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)) ⊆ (Finset.Ioc 0 N) := by
      intro n hn
      simp only [Finset.mem_filter] at hn
      rw [Finset.mem_Ioc]; exact ⟨hn.2.2, hN hn.2.1⟩
    have := Finset.card_le_card this
    simp only [Nat.card_Ioc, Nat.sub_zero] at this
    exact_mod_cast this
  have hsx : (N : ℝ) + 1 ≤ √x := by
    apply Real.le_sqrt_of_sq_le; exact le_max_right _ _
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- `a_{A(x)} ≤ x`. -/
theorem nth_AS_le (h0 : 0 ∈ S) (hinf : S.Infinite) {x : ℝ} (hx : 0 ≤ x) :
    (Nat.nth (· ∈ S) ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card : ℝ) ≤ x := by
  have h := (Nat.lt_nth_iff_count_lt (p := (· ∈ S)) hinf
    (a := ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card) (b := ⌊x⌋₊ + 1)).mp
    (by rw [count_eq S h0]; omega)
  have h' : Nat.nth (· ∈ S) ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card ≤ ⌊x⌋₊ := by
    omega
  calc (Nat.nth (· ∈ S) _ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h'
    _ ≤ x := Nat.floor_le hx

/-- **`a_k` form.** `liminf a_k/k² ≤ α`: no `c > α` has `c k² ≤ a_k` for all large `k`. -/
theorem erdos271_ak (h0 : 0 ∈ S) (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ c : ℝ, Real.log (1 + √2) / (2 * √2) < c →
      ¬ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ Nat.nth (· ∈ S) k := by
  intro c hc hev
  have hinf := infinite_of_cover S s hcov
  have ha := alpha_pos
  change α < c at hc
  have hc0 : 0 < c := lt_trans ha hc
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  -- U strictly between 1/√c and 1/√α
  have hsc : √α < √c := Real.sqrt_lt_sqrt ha.le hc
  have hsa := Real.sqrt_pos.mpr ha
  have hscp := Real.sqrt_pos.mpr hc0
  set U : ℝ := (1 / √c + 1 / √α) / 2 with hUdef
  have h1 : 1 / √c < 1 / √α := one_div_lt_one_div_of_lt hsa hsc
  have hUlt : U < 1 / √α := by rw [hUdef]; linarith
  have hUgt : 1 / √c < U := by rw [hUdef]; linarith
  have hUpos : 0 < U := lt_trans (by positivity) hUgt
  apply erdos271_limsup S h0 s hcov U hUlt
  filter_upwards [eventually_ge_atTop (((K : ℝ) / U) ^ 2)] with x hx
  have hx0 : 0 ≤ x := le_trans (sq_nonneg _) hx
  set n := ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card with hn
  show (n : ℝ) ≤ U * √x
  have hsx : (K : ℝ) / U ≤ √x := Real.le_sqrt_of_sq_le hx
  by_cases hnK : n < K
  · have : (n : ℝ) ≤ K := by exact_mod_cast hnK.le
    have : (K : ℝ) ≤ U * √x := by rwa [div_le_iff₀ hUpos, mul_comm] at hsx
    linarith
  · push Not at hnK
    have hak := hK n hnK
    have hle := nth_AS_le S h0 hinf hx0
    rw [← hn] at hle
    have hcn : c * (n : ℝ) ^ 2 ≤ x := le_trans hak hle
    -- √c · n ≤ √x
    have hq : (√c * n) ^ 2 ≤ (√x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hx0]; exact hcn
    have hq' : √c * n ≤ √x :=
      (pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg _) two_ne_zero).mp hq
    have hUc : 1 ≤ U * √c := by
      have := (div_lt_iff₀ hscp).mp hUgt; linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    calc (n : ℝ) ≤ U * √c * n := le_mul_of_one_le_left hn0 hUc
      _ = U * (√c * n) := by ring
      _ ≤ U * √x := mul_le_mul_of_nonneg_left hq' hUpos.le

end Erdos271.Final
