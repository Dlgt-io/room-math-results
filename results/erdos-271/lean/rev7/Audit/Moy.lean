import Mathlib

/-!
# Writeup Lemma 1 (Moy-type count), finite form

If `P ⊆ [0, X]` is finite and every omitted `z ∈ (s, X]` is `2b - a` with `a < b` in `P`, then
`2X ≤ A² + 3A + 2s`, where `A = #{p ∈ P : 0 < p ≤ X}`.
The set version applies this to `P = S ∩ [0, X]` for a weak AP3-covering set `S`.
-/

open Finset

namespace Erdos271.Moy

/-- Ordered pairs `a < b` from `P`. -/
def pairs (P : Finset ℕ) : Finset (ℕ × ℕ) := (P ×ˢ P).filter (fun q => q.1 < q.2)

/-- `#pairs ≤ C(|P|, 2)`. -/
theorem card_pairs_le (P : Finset ℕ) : (pairs P).card ≤ P.card.choose 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun q => ({q.1, q.2} : Finset ℕ))
  · intro q hq
    simp only [pairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair (ne_of_lt hq.2)⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hq.1.1
    · exact hq.1.2
  · intro q hq q' hq' heq
    simp only [pairs, Finset.mem_coe, Finset.mem_filter] at hq hq'
    simp only at heq
    have h1 : q.1 ∈ ({q'.1, q'.2} : Finset ℕ) := by
      rw [← heq]; simp
    have h2 : q.2 ∈ ({q'.1, q'.2} : Finset ℕ) := by
      rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    have := hq.2; have := hq'.2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · omega
    · exact Prod.ext h1 h2
    · omega
    · omega

/-- Distinct omitted integers need distinct witness pairs. -/
theorem omitted_le_pairs (P : Finset ℕ) (s X : ℕ)
    (hcov : ∀ z ∈ Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z) :
    ((Ioc s X).filter (fun z => z ∉ P)).card ≤ (pairs P).card := by
  classical
  have hw : ∀ z ∈ (Ioc s X).filter (fun z => z ∉ P),
      ∃ q : ℕ × ℕ, q ∈ pairs P ∧ 2 * q.2 - q.1 = z := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨a, ha, b, hb, hab, h⟩ := hcov z hz.1 hz.2
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, h⟩
  choose! f hf using hw
  apply Finset.card_le_card_of_injOn f
  · intro z hz; exact (hf z hz).1
  · intro z hz z' hz' heq
    have e1 := (hf z hz).2
    have e2 := (hf z' hz').2
    rw [← e1, ← e2, heq]

/-- **Lemma 1, finite form.** -/
theorem moy_finite (P : Finset ℕ) (s X : ℕ) (hPX : ∀ p ∈ P, p ≤ X)
    (hcov : ∀ z ∈ Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z) :
    2 * X ≤ ((P.filter (fun p => 0 < p ∧ p ≤ X)).card) ^ 2
      + 3 * (P.filter (fun p => 0 < p ∧ p ≤ X)).card + 2 * s := by
  classical
  set A := (P.filter (fun p => 0 < p ∧ p ≤ X)).card with hA
  -- |P| ≤ A + 1
  have hP : P.card ≤ A + 1 := by
    have hsub : P ⊆ insert 0 (P.filter (fun p => 0 < p ∧ p ≤ X)) := by
      intro p hp
      rcases Nat.eq_zero_or_pos p with h | h
      · rw [h]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, h, hPX p hp⟩)
    calc P.card ≤ (insert 0 (P.filter (fun p => 0 < p ∧ p ≤ X))).card := Finset.card_le_card hsub
      _ ≤ A + 1 := Finset.card_insert_le _ _
  -- members of P in (s, X] are at most A
  have hmem : ((Ioc s X).filter (fun z => z ∈ P)).card ≤ A := by
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hz ⊢
    exact ⟨hz.2, by omega, hz.1.2⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ioc s X) (fun z => z ∈ P)
  have hIoc : (Ioc s X).card = X - s := Nat.card_Ioc s X
  have hom := le_trans (omitted_le_pairs P s X hcov) (card_pairs_le P)
  have hch : P.card.choose 2 ≤ (A + 1).choose 2 := Nat.choose_le_choose 2 hP
  have hc2 : 2 * (A + 1).choose 2 = (A + 1) * A := by
    rw [Nat.choose_two_right]
    have : 2 ∣ (A + 1) * A := by
      rcases Nat.even_or_odd A with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨(A + 1) * k, by rw [hk]; ring⟩
      · exact ⟨(k + 1) * A, by rw [hk]; ring⟩
    simp only [Nat.add_sub_cancel]
    exact Nat.mul_div_cancel' this
  have key : X - s ≤ (A + 1).choose 2 + A := by omega
  have hsq : (A + 1) * A = A ^ 2 + A := by ring
  rw [hsq] at hc2
  generalize A ^ 2 = B at hc2 ⊢
  omega

/-- **Lemma 1 for a set** `S ⊆ ℕ` that covers every omitted `z > s`: for every `X`,
`2X ≤ A(X)² + 3A(X) + 2s` with `A(X) = #{p ∈ S : 0 < p ≤ X}`. -/
theorem moy_set (S : Set ℕ) [DecidablePred (· ∈ S)] (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) (X : ℕ) :
    2 * X ≤ (((range (X + 1)).filter (· ∈ S)).filter (fun p => 0 < p ∧ p ≤ X)).card ^ 2
      + 3 * (((range (X + 1)).filter (· ∈ S)).filter (fun p => 0 < p ∧ p ≤ X)).card
      + 2 * s := by
  apply moy_finite
  · intro p hp
    have := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_range] at this; omega
  · intro z hz hzP
    rw [Finset.mem_Ioc] at hz
    have hzS : z ∉ S := by
      intro h; apply hzP
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
    obtain ⟨a, ha, b, hb, hab, h⟩ := hcov z hz.1 hzS
    have hbz : b < z := by omega
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ha⟩,
      b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hb⟩, hab, h⟩

/-- Real-valued consequence: `A(X) + 3/2 ≥ √(2(X - s))` for `X ≥ s`. -/
theorem moy_sqrt (A s X : ℕ) (h : 2 * X ≤ A ^ 2 + 3 * A + 2 * s) :
    Real.sqrt (2 * ((X : ℝ) - s)) ≤ (A : ℝ) + 3 / 2 := by
  have h' : (2 * X : ℝ) ≤ (A : ℝ) ^ 2 + 3 * A + 2 * s := by exact_mod_cast h
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith

end Erdos271.Moy

#print axioms Erdos271.Moy.card_pairs_le
#print axioms Erdos271.Moy.omitted_le_pairs
#print axioms Erdos271.Moy.moy_finite
#print axioms Erdos271.Moy.moy_set
#print axioms Erdos271.Moy.moy_sqrt
