import LiminfCore

/-!
# Claude's liminf construction (#127): stacking and the final theorem

There is a (strong) `AP₃`-covering set `A ⊆ ℕ` (every `n ≥ 3` is `2b - a` with `0 < a < b < n`,
`a, b ∈ A`) with `liminf A(n)/√n ≤ 53√3/48`: for every `ε > 0` and `N` there is `n ≥ N` with
`|A ∩ [0,n]| ≤ (53√3/48 + ε)√n`.

Stacking: stage `k` is `R_k = T_{k²}` (lift-and-fix from `S₇₆₈`), covering `[3, Y_k]` with
`Y_k = 4^{k²}·768`, translated by `t_k` (`t_0 = 0`, `t_{k+1} = t_k + Y_k - 3`).
-/

open Finset Real

namespace Erdos271.Liminf

def R (k : ℕ) : Finset ℕ := iter S768 (k * k)

def Y (k : ℕ) : ℕ := 4 ^ (k * k) * 768

def t : ℕ → ℕ
  | 0 => 0
  | k + 1 => t k + Y k - 3

/-- The stacked set. -/
def Aset : Set ℕ := {m | ∃ k, ∃ r ∈ R k, m = r + t k}

theorem R_spec (k : ℕ) :
    Cov (R k) 3 (Y k) ∧ (∀ x ∈ R k, 1 ≤ x) ∧ (R k).card + 3 = 2 ^ (k * k) * 53 := by
  obtain ⟨h1, -, -, h4, h5⟩ :=
    iter_spec S768 768 (by norm_num) S768_cov S768_small.1 S768_small.2.1 S768_pos (k * k)
  exact ⟨h1, h4, by unfold R; rw [h5, S768_card]⟩

theorem Y_ge (k : ℕ) : 768 ≤ Y k := Nat.le_mul_of_pos_left _ (by positivity)

theorem le_Y (n : ℕ) : n ≤ Y n := by
  have h1 : n < 4 ^ n := Nat.lt_pow_self (by norm_num)
  have h2 : 4 ^ n ≤ 4 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self n)
  have h3 : 4 ^ (n * n) ≤ 4 ^ (n * n) * 768 := Nat.le_mul_of_pos_right _ (by norm_num)
  unfold Y; omega

theorem t_succ (k : ℕ) : t (k + 1) + 3 = t k + Y k := by
  have := Y_ge k
  simp only [t]; omega

theorem t_mono : Monotone t :=
  monotone_nat_of_le_succ fun k => by have := t_succ k; have := Y_ge k; omega

theorem stage_cov (k n : ℕ) (h1 : t k + 3 ≤ n) (h2 : n ≤ t k + Y k) :
    ∃ a ∈ Aset, ∃ b ∈ Aset, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
  obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := (R_spec k).1 (n - t k) (by omega) (by omega)
  exact ⟨a + t k, ⟨k, a, ha, rfl⟩, b + t k, ⟨k, b, hb, rfl⟩, by omega, by omega, by omega,
    by omega⟩

/-- **Covering.** Every `n ≥ 3` is `2b - a`, `0 < a < b < n`, `a, b ∈ A` (so `n₀ = 2`). -/
theorem covering : ∀ n, 3 ≤ n → ∃ a ∈ Aset, ∃ b ∈ Aset, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
  intro n hn
  classical
  have hex : ∃ k, n ≤ t k + Y k := ⟨n, by have := le_Y n; omega⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, n ≤ t k + Y k ∧ ∀ i < k, ¬ n ≤ t i + Y i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  cases k with
  | zero => exact stage_cov 0 n (by simp only [t]; omega) hk
  | succ p =>
    exact stage_cov (p + 1) n (by have := hmin p (by omega); have := t_succ p; omega) hk

/-- Finite superset of `A ∩ [0, x_k]`: stages `≤ k`, plus `t_{k+1} + {1,2,3}`. -/
def F (k : ℕ) : Finset ℕ :=
  ((range (k + 1)).biUnion fun i => (R i).image (· + t i)) ∪
    ({1, 2, 3} : Finset ℕ).image (· + t (k + 1))

theorem sub_F (k : ℕ) : Aset ∩ Set.Iic (t k + Y k) ⊆ ↑(F k) := by
  rintro m ⟨⟨i, r, hr, rfl⟩, hm⟩
  simp only [Set.mem_Iic] at hm
  rw [Finset.mem_coe]
  have hr1 := (R_spec i).2.1 r hr
  rcases lt_trichotomy i (k + 1) with h | h | h
  · refine Finset.mem_union_left _ ?_
    rw [mem_biUnion]
    exact ⟨i, mem_range.2 h, mem_image.2 ⟨r, hr, rfl⟩⟩
  · subst h
    refine Finset.mem_union_right _ ?_
    have := t_succ k
    rw [mem_image]
    refine ⟨r, ?_, rfl⟩
    simp only [mem_insert, mem_singleton]
    omega
  · exfalso
    have hm2 : t (k + 1 + 1) ≤ t i := t_mono (by omega)
    have := t_succ (k + 1)
    have := t_succ k
    have := Y_ge (k + 1)
    omega

theorem card_F (k : ℕ) : (F k).card ≤ (∑ i ∈ range (k + 1), (R i).card) + 3 := by
  calc (F k).card ≤ ((range (k + 1)).biUnion fun i => (R i).image (· + t i)).card +
        (({1, 2, 3} : Finset ℕ).image (· + t (k + 1))).card := card_union_le _ _
    _ ≤ (∑ i ∈ range (k + 1), (R i).card) + 3 := by
        apply add_le_add
        · exact card_biUnion_le.trans (sum_le_sum fun i _ => card_image_le)
        · exact card_image_le.trans (by decide)

/-- Counting function `A(n) = |A ∩ [0,n]|`. -/
noncomputable def cnt (n : ℕ) : ℕ := (Aset ∩ Set.Iic n).ncard

theorem cnt_le (k : ℕ) : cnt (t k + Y k) ≤ (F k).card := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (sub_F k) (Finset.finite_toSet _)

theorem geom (m : ℕ) : ∑ i ∈ range (m + 1), 2 ^ (i * i) < 2 ^ (m * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : 2 ^ (m * m + 1) ≤ 2 ^ ((m + 1) * (m + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ ((m + 1) * (m + 1) + 1) = 2 * 2 ^ ((m + 1) * (m + 1)) := by ring
    omega

/-- **Earlier stages are `o(√Y)`.** `A(x_{m+1}) ≤ 53·2^{(m+1)²} + 56·2^{m²+1}`. -/
theorem cnt_bound (m : ℕ) :
    cnt (t (m + 1) + Y (m + 1)) ≤ 53 * 2 ^ ((m + 1) * (m + 1)) + 56 * 2 ^ (m * m + 1) := by
  have h1 := cnt_le (m + 1)
  have h2 := card_F (m + 1)
  have h3 : ∑ i ∈ range (m + 1 + 1), (R i).card ≤ ∑ i ∈ range (m + 1 + 1), 53 * 2 ^ (i * i) :=
    sum_le_sum fun i _ => by have := (R_spec i).2.2; omega
  have h4 : ∑ i ∈ range (m + 1 + 1), 53 * 2 ^ (i * i) =
      53 * (∑ i ∈ range (m + 1), 2 ^ (i * i)) + 53 * 2 ^ ((m + 1) * (m + 1)) := by
    rw [sum_range_succ, mul_sum]
  have h5 := geom m
  have h6 : 1 ≤ 2 ^ (m * m + 1) := Nat.one_le_two_pow
  omega

theorem pow_split (m : ℕ) : (2 : ℝ) ^ ((m + 1) * (m + 1)) = 2 ^ (m * m + 1) * 4 ^ m := by
  rw [show (m + 1) * (m + 1) = (m * m + 1) + 2 * m by ring, pow_add, pow_mul]
  norm_num

/-- **Main theorem (Claude #127, formalised).** A strong `AP₃`-covering set with
`liminf |A ∩ [0,n]| / √n ≤ 53√3/48`. -/
theorem liminf_construction :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
        ((A ∩ Set.Iic n).ncard : ℝ) ≤ (53 * √3 / 48 + ε) * √(n : ℝ) := by
  refine ⟨Aset, covering, ?_⟩
  intro ε hε N
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℕ, 56 / ε < 4 ^ m0 := pow_unbounded_of_one_lt _ (by norm_num)
  set m := max m0 N with hm
  refine ⟨t (m + 1) + Y (m + 1), ?_, ?_⟩
  · have := le_Y (m + 1); have := le_max_right m0 N; omega
  · set P : ℝ := (2 : ℝ) ^ ((m + 1) * (m + 1)) with hP
    set Q : ℝ := (2 : ℝ) ^ (m * m + 1) with hQ
    have hc : ((cnt (t (m + 1) + Y (m + 1)) : ℕ) : ℝ) ≤ 53 * P + 56 * Q := by
      have := cnt_bound m
      rw [hP, hQ]; exact_mod_cast this
    have hPQ : P = Q * 4 ^ m := pow_split m
    have hQ0 : 0 < Q := by positivity
    have h4 : (4 : ℝ) ^ m0 ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have h56 : 56 < ε * 4 ^ m := by
      have := (div_lt_iff₀ hε).1 hm0
      nlinarith
    have hQP : 56 * Q ≤ ε * P := by rw [hPQ]; nlinarith
    -- `√x ≥ 16√3·P`
    have hx : (768 : ℝ) * P ^ 2 ≤ ((t (m + 1) + Y (m + 1) : ℕ) : ℝ) := by
      have hn : 768 * (2 ^ ((m + 1) * (m + 1))) ^ 2 ≤ t (m + 1) + Y (m + 1) := by
        have e : (2 ^ ((m + 1) * (m + 1))) ^ 2 = 4 ^ ((m + 1) * (m + 1)) := by
          rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num
        rw [e]; unfold Y; omega
      rw [hP]; exact_mod_cast hn
    have s3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have s0 : 0 ≤ √3 := Real.sqrt_nonneg 3
    have s1 : 1 ≤ √3 := by nlinarith
    have hsq : 16 * √3 * P ≤ √((t (m + 1) + Y (m + 1) : ℕ) : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hP0 : 0 < P := by positivity
    calc ((Aset ∩ Set.Iic (t (m + 1) + Y (m + 1))).ncard : ℝ)
        = ((cnt (t (m + 1) + Y (m + 1)) : ℕ) : ℝ) := rfl
      _ ≤ 53 * P + ε * P := by linarith
      _ ≤ (53 * √3 / 48 + ε) * (16 * √3 * P) := by nlinarith
      _ ≤ (53 * √3 / 48 + ε) * √((t (m + 1) + Y (m + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Fidelity: `A ∩ [0,n]` is finite, so `ncard` is its true cardinality; `0 ∉ A`. -/
theorem count_finite (n : ℕ) : (Aset ∩ Set.Iic n).Finite := (Set.finite_Iic n).inter_of_right _

theorem zero_not_mem : 0 ∉ Aset := by
  rintro ⟨k, r, hr, h⟩
  have := (R_spec k).2.1 r hr
  omega

end Erdos271.Liminf
