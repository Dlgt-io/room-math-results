import Audit.Glue6
import Audit.MemberTail

/-!
# Natural ↔ real prefix bridge

For `P : Finset ℕ` with `0 ∈ P`, let `Pr P ⊂ ℝ` be the positive part of `P`, cast to `ℝ`.
* `W_eq_weightedPairs`: Grok's `W P` (Lemma 2, over ℕ) equals ChatGPT's `weightedPairs (Pr P)`
  (finite identity, over ℝ): the pairs `(0, b)` give the terms `1/(2b)`.
* `Acount_Pr`: `Acount (Pr P) t = Acnt P t` at natural `t`, so a real envelope gives the
  natural envelope needed by `member_tail` / `lemma2_full`.
* `Pr_mem`, `card_Pr`: `Pr P ⊂ [1, X]` and `#Pr P = A(X)` when `P ⊆ [0, X]`.
-/

open MeasureTheory Set Real Finset
open Erdos271.FiniteIntegrals

namespace Erdos271.Glue

/-- Positive part of `P`, cast to `ℝ`. -/
noncomputable def Pr (P : Finset ℕ) : Finset ℝ := (P.filter (fun n => 0 < n)).image (fun n : ℕ => (n : ℝ))

theorem cast_injOn (s : Finset ℕ) : Set.InjOn (fun n : ℕ => (n : ℝ)) (s : Set ℕ) :=
  fun _ _ _ _ h => Nat.cast_injective h

theorem Pr_mem (P : Finset ℕ) {X : ℕ} (hPX : ∀ p ∈ P, p ≤ X) :
    ∀ p ∈ Pr P, 1 ≤ p ∧ p ≤ (X : ℝ) := by
  intro p hp
  simp only [Pr, Finset.mem_image, Finset.mem_filter] at hp
  obtain ⟨n, ⟨hn, hn0⟩, rfl⟩ := hp
  exact ⟨by exact_mod_cast hn0, by exact_mod_cast hPX n hn⟩

theorem Acount_Pr (P : Finset ℕ) (t : ℕ) :
    Acount (Pr P) (t : ℝ) = (Erdos271.MemberTail.Acnt P t : ℝ) := by
  unfold Acount Pr Erdos271.MemberTail.Acnt
  rw [Finset.sum_image (cast_injOn _)]
  simp only [Set.indicator, Set.mem_Ici, Nat.cast_le]
  rw [Finset.sum_boole, Finset.filter_filter]

theorem card_Pr (P : Finset ℕ) {X : ℕ} (hPX : ∀ p ∈ P, p ≤ X) :
    ((Pr P).card : ℝ) = (Erdos271.MemberTail.Acnt P X : ℝ) := by
  unfold Pr Erdos271.MemberTail.Acnt
  rw [Finset.card_image_of_injOn (cast_injOn _)]
  congr 2
  apply Finset.filter_congr
  intro n hn
  simp [hPX n hn]

theorem W_eq_weightedPairs (P : Finset ℕ) (h0 : 0 ∈ P) :
    Erdos271.WeightedCover.W P = weightedPairs (Pr P) := by
  classical
  set Pp := P.filter (fun n => 0 < n) with hPp
  have hW : Erdos271.WeightedCover.W P
      = ∑ a ∈ P, ∑ b ∈ P, if a < b then (((2 * b - a : ℕ) : ℝ))⁻¹ else 0 := by
    unfold Erdos271.WeightedCover.W Erdos271.WeightedCover.pairs Erdos271.WeightedCover.tgt
    rw [Finset.sum_filter, Finset.sum_product]
  have hzero : P.filter (fun n => ¬ 0 < n) = {0} := by
    ext n; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; omega
    · rintro rfl; exact ⟨h0, lt_irrefl 0⟩
  rw [hW, ← Finset.sum_filter_add_sum_filter_not P (fun n => 0 < n), hzero,
    Finset.sum_singleton]
  unfold weightedPairs Pr
  rw [Finset.sum_image (cast_injOn _), Finset.sum_image (cast_injOn _), add_comm]
  congr 1
  · -- the pairs (0, b)
    rw [← Finset.sum_filter_add_sum_filter_not P (fun n => 0 < n), hzero, Finset.sum_singleton]
    simp only [lt_irrefl, if_false, add_zero]
    rw [← hPp]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    have hb0 : 0 < b := (Finset.mem_filter.mp hb).2
    simp only [hb0, if_true, Nat.sub_zero]
    push_cast; ring
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    have ha0 : 0 < a := (Finset.mem_filter.mp ha).2
    rw [Finset.sum_image (cast_injOn _),
      ← Finset.sum_filter_add_sum_filter_not P (fun n => 0 < n), hzero, Finset.sum_singleton]
    have : ¬ a < 0 := by omega
    simp only [this, if_false, add_zero]
    rw [← hPp]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    unfold forwardPairWeight
    by_cases hab : a < b
    · have hab' : (a : ℝ) < b := by exact_mod_cast hab
      rw [if_pos hab, if_pos hab', Nat.cast_sub (by omega)]
      push_cast; ring
    · have hab' : ¬ (a : ℝ) < b := by exact_mod_cast hab
      rw [if_neg hab, if_neg hab']

/-- The real envelope on `[x0, X]` gives the natural envelope used by `member_tail`. -/
theorem env_nat (P : Finset ℕ) {L U : ℝ} {x0 X : ℕ}
    (henv : ∀ x ∈ Icc (x0 : ℝ) X, L * √x ≤ Acount (Pr P) x ∧ Acount (Pr P) x ≤ U * √x) :
    ∀ t : ℕ, x0 ≤ t → t ≤ X → (Erdos271.MemberTail.Acnt P t : ℝ) ≤ U * √(t : ℝ) := by
  intro t h1 h2
  rw [← Acount_Pr]
  exact (henv t ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩).2

end Erdos271.Glue
