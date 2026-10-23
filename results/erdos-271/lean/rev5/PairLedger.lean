import Mathlib
namespace Erdos271.FiniteIntegrals

theorem finite_pair_ledger :
∀ P : Finset Real, ∀ X : Real, ∀ I : Real → Real → Real, ∀ J : Real → Real → Real, ∀ D : Real → Real, ∀ Z : Real → Real, ∀ W : Real → Real → Real, 0 < X → (∀ p : Real, Membership.mem P p → 0 < p ∧ p ≤ X) → (∀ p : Real, ∀ q : Real, I p q = 1 / max p q - 1 / X) → (∀ p : Real, ∀ q : Real, J p q = 1 / (2 * max p q) - 1 / (2 * X) + 1 / (4 * (2 * X - p)) - 1 / (4 * (2 * max p q - p))) → (∀ p : Real, D p = 1 / (2 * X - p)) → (∀ p : Real, Z p = 1 / (2 * p)) → (∀ p : Real, ∀ q : Real, W p q = ite (p < q) (1 / (2 * q - p)) 0) → Finset.sum P Z + Finset.sum P (Function.comp (Finset.sum P) W) = (3 / 2) * Finset.sum P (Function.comp (Finset.sum P) I) - 4 * Finset.sum P (Function.comp (Finset.sum P) J) + ((Finset.card P : Real) * Finset.sum P D - (Finset.card P : Real) ^ 2 / (2 * X)) ∧ 0 ≤ (Finset.card P : Real) * Finset.sum P D - (Finset.card P : Real) ^ 2 / (2 * X) ∧ (Finset.card P : Real) * Finset.sum P D - (Finset.card P : Real) ^ 2 / (2 * X) ≤ (Finset.card P : Real) ^ 2 / (2 * X) := by
  classical
  intro P X I J D Z W hX hP hI hJ hD hZ hW
  let C : Real → Real → Real := fun p q =>
    1 / (2 * max p q - p) - 1 / (2 * max p q)
  let T : Real → Real → Real := fun p q =>
    (if q = p then Z p else 0) + W p q
  have hcdiag (p : Real) : C p p = Z p := by
    rw [hZ p]
    dsimp [C]
    rw [max_self, show 2 * p - p = p by ring]
    simp only [one_div, mul_inv_rev]
    norm_num
    ring
  have hcoff (p q : Real) (hpq : p < q) : C p q + C q p = 1 / (2 * q - p) := by
    dsimp [C]
    rw [max_eq_right hpq.le, max_eq_left hpq.le]
    rw [show 2 * q - q = q by ring]
    simp only [one_div, mul_inv_rev]
    norm_num
    ring
  have htdiag (p : Real) : T p p = Z p := by simp [T, hW]
  have htoff (p q : Real) (hpq : p < q) : T p q + T q p = 1 / (2 * q - p) := by
    simp [T, hW, hpq, hpq.ne, hpq.ne', not_lt_of_ge hpq.le]
  have hpair (p q : Real) : C p q + C q p = T p q + T q p := by
    rcases lt_trichotomy p q with h | h | h
    · rw [hcoff p q h, htoff p q h]
    · subst q
      rw [hcdiag, htdiag]
    · rw [add_comm (C p q), add_comm (T p q), hcoff q p h, htoff q p h]
  have hs : (P.sum fun p => P.sum fun q => C p q) =
      (P.sum fun p => P.sum fun q => T p q) := by
    have hh : (P.sum fun p => P.sum fun q => C p q + C q p) =
        (P.sum fun p => P.sum fun q => T p q + T q p) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact hpair p q
    simp only [Finset.sum_add_distrib] at hh
    have hC : (P.sum fun p => P.sum fun q => C q p) =
        (P.sum fun p => P.sum fun q => C p q) := Finset.sum_comm
    have hT : (P.sum fun p => P.sum fun q => T q p) =
        (P.sum fun p => P.sum fun q => T p q) := Finset.sum_comm
    rw [hC, hT] at hh
    linarith
  have htSum : (P.sum fun p => P.sum fun q => T p q) =
      P.sum Z + P.sum (fun p => P.sum (fun q => W p q)) := by
    dsimp [T]
    simp only [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  have hlocal (p q : Real) :
      (3 / 2 : Real) * I p q - 4 * J p q + (D p - 1 / (2 * X)) = C p q := by
    rw [hI p q, hJ p q, hD p]
    dsimp [C]
    simp only [one_div, mul_inv_rev]
    norm_num
    ring
  have hsumlocal :
      (P.sum fun p => P.sum fun q => (3 / 2 : Real) * I p q - 4 * J p q + (D p - 1 / (2 * X))) =
      P.sum (fun p => P.sum (fun q => C p q)) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact hlocal p q
  have hconst : (P.sum fun p => P.sum fun _q => D p - 1 / (2 * X)) =
      (P.card : Real) * P.sum D - (P.card : Real) ^ 2 / (2 * X) := by
    simp only [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  have hledger : P.sum Z + P.sum (fun p => P.sum (fun q => W p q)) =
      (3 / 2 : Real) * P.sum (fun p => P.sum (fun q => I p q)) -
      4 * P.sum (fun p => P.sum (fun q => J p q)) +
      ((P.card : Real) * P.sum D - (P.card : Real) ^ 2 / (2 * X)) := by
    rw [← htSum, ← hs, ← hsumlocal]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hconst]
    simp only [Finset.sum_sub_distrib]
  have hlo : (P.card : Real) / (2 * X) ≤ P.sum D := by
    calc
      _ = P.sum (fun _ : Real => 1 / (2 * X)) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        rw [hD p]
        exact one_div_le_one_div_of_le
          (by linarith [(hP p hp).2] : 0 < 2 * X - p)
          (by linarith [(hP p hp).1] : 2 * X - p ≤ 2 * X)
  have hhi : P.sum D ≤ (P.card : Real) / X := by
    calc
      _ ≤ P.sum (fun _ : Real => 1 / X) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [hD p]
        exact one_div_le_one_div_of_le hX (by linarith [(hP p hp).2])
      _ = _ := by simp; ring
  have hm : 0 ≤ (P.card : Real) := Nat.cast_nonneg _
  have hmullo := mul_le_mul_of_nonneg_left hlo hm
  have hmulhi := mul_le_mul_of_nonneg_left hhi hm
  have hdiv : (P.card : Real) ^ 2 / X = 2 * ((P.card : Real) ^ 2 / (2 * X)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num
    ring
  have hlo' : (P.card : Real) ^ 2 / (2 * X) ≤ (P.card : Real) * P.sum D := by
    calc
      _ = (P.card : Real) * ((P.card : Real) / (2 * X)) := by ring
      _ ≤ _ := hmullo
  have hhi' : (P.card : Real) * P.sum D ≤ (P.card : Real) ^ 2 / X := by
    calc
      _ ≤ (P.card : Real) * ((P.card : Real) / X) := hmulhi
      _ = _ := by ring
  refine ⟨hledger, sub_nonneg.mpr hlo', ?_⟩
  linarith

end Erdos271.FiniteIntegrals
