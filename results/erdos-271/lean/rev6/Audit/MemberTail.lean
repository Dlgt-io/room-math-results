import Mathlib
import Audit.WCover

/-!
# Members' reciprocal tail (writeup Lemma 2, last step) and the full finite Lemma 2

Envelope hypothesis: `A(t) = #{p ∈ P : 0 < p ≤ t} ≤ U √t` for natural `t ∈ [x0, X]`.
Conclusion: `∑_{p ∈ P, x0 < p ≤ X} 1/p ≤ 2U/√x0`.
Proof: discrete Abel summation by induction on the largest element, using
`k (1/a - 1/T) ≤ 2U (1/√a - 1/√T)` whenever `0 < a ≤ T` and `k ≤ U √a`.
-/

open Finset Real

namespace Erdos271.MemberTail

/-- Key one-step inequality. -/
theorem step_ineq {U a T k : ℝ} (ha : 0 < a) (haT : a ≤ T) (hk0 : 0 ≤ k)
    (hk : k ≤ U * √a) :
    k * (1 / a - 1 / T) ≤ 2 * U * (1 / √a - 1 / √T) := by
  have hT : 0 < T := lt_of_lt_of_le ha haT
  set u := √a with hu
  set v := √T with hv
  have hu0 : 0 < u := Real.sqrt_pos.mpr ha
  have hv0 : 0 < v := Real.sqrt_pos.mpr hT
  have huv : u ≤ v := Real.sqrt_le_sqrt haT
  have hau : a = u ^ 2 := (Real.sq_sqrt ha.le).symm
  have hTv : T = v ^ 2 := (Real.sq_sqrt hT.le).symm
  have hdiff : 0 ≤ 1 / a - 1 / T := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha haT
  have hU : 0 ≤ U := by
    by_contra h; push Not at h
    have : U * u < 0 := mul_neg_of_neg_of_pos h hu0
    linarith
  calc k * (1 / a - 1 / T) ≤ (U * u) * (1 / a - 1 / T) :=
        mul_le_mul_of_nonneg_right hk hdiff
    _ ≤ 2 * U * (1 / u - 1 / v) := by
        rw [hau, hTv]
        have key : u * (1 / u ^ 2 - 1 / v ^ 2) ≤ 2 * (1 / u - 1 / v) := by
          have e1 : u * (1 / u ^ 2 - 1 / v ^ 2) = ((v - u) * (v + u)) / (u * v ^ 2) := by
            field_simp; ring
          have e2 : 2 * (1 / u - 1 / v) = (2 * (v - u) * v) / (u * v ^ 2) := by
            field_simp
          rw [e1, e2]
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr huv)]
        calc U * u * (1 / u ^ 2 - 1 / v ^ 2) = U * (u * (1 / u ^ 2 - 1 / v ^ 2)) := by ring
          _ ≤ U * (2 * (1 / u - 1 / v)) := mul_le_mul_of_nonneg_left key hU
          _ = 2 * U * (1 / u - 1 / v) := by ring

/-- Strengthened Abel bound, by induction on the maximum. Ranks are taken inside `Q`. -/
theorem abel_core (U x0 : ℝ) (hU : 0 ≤ U) (hx0 : 0 < x0) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, x0 < (q : ℝ))
    (hrank : ∀ q ∈ Q, ((Q.filter (fun p => p ≤ q)).card : ℝ) ≤ U * √(q : ℝ)) :
    ∀ T : ℝ, (∀ q ∈ Q, (q : ℝ) ≤ T) → x0 ≤ T →
      ∑ q ∈ Q, ((q : ℝ))⁻¹ ≤ 2 * U / √x0 - 2 * U / √T + (Q.card : ℝ) / T := by
  classical
  induction Q using Finset.induction_on_max with
  | empty =>
    intro T _ hT
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_div, add_zero]
    have h1 : √x0 ≤ √T := Real.sqrt_le_sqrt hT
    have h2 : 0 < √x0 := Real.sqrt_pos.mpr hx0
    have : 2 * U / √T ≤ 2 * U / √x0 :=
      div_le_div_of_nonneg_left (by positivity) h2 h1
    linarith
  | insert a s hlt ih =>
    intro T hle hT
    have has : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha0 : x0 < (a : ℝ) := hQ a (Finset.mem_insert_self a s)
    have hapos : 0 < (a : ℝ) := lt_trans hx0 ha0
    have haT : (a : ℝ) ≤ T := hle a (Finset.mem_insert_self a s)
    -- ranks in s agree with ranks in insert a s
    have hfilt : ∀ q ∈ s, (insert a s).filter (fun p => p ≤ q) = s.filter (fun p => p ≤ q) := by
      intro q hq
      rw [Finset.filter_insert]
      have : ¬ a ≤ q := not_le.mpr (hlt q hq)
      simp [this]
    have ih' := ih (fun q hq => hQ q (Finset.mem_insert_of_mem hq))
      (fun q hq => by rw [← hfilt q hq]; exact hrank q (Finset.mem_insert_of_mem hq))
      (a : ℝ) (fun q hq => by exact_mod_cast (hlt q hq).le) ha0.le
    -- rank of a is |s| + 1
    have hfa : (insert a s).filter (fun p => p ≤ a) = insert a s := by
      apply Finset.filter_true_of_mem
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact le_refl _
      · exact (hlt x hx).le
    have hka : ((s.card : ℝ) + 1) ≤ U * √(a : ℝ) := by
      have := hrank a (Finset.mem_insert_self a s)
      rw [hfa, Finset.card_insert_of_notMem has] at this
      push_cast at this; exact this
    have hstep := step_ineq hapos haT (by positivity) hka
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has]
    push_cast
    have e1 : (s.card : ℝ) / a + (a : ℝ)⁻¹ = ((s.card : ℝ) + 1) * (1 / a) := by
      field_simp
    have e2 : ((s.card : ℝ) + 1) / T = ((s.card : ℝ) + 1) * (1 / T) := by ring
    have e3 : 2 * U / √(a : ℝ) - 2 * U / √T = 2 * U * (1 / √(a : ℝ) - 1 / √T) := by ring
    nlinarith [hstep, ih', e1, e2, e3]

/-- Counting function of `P` (members `0 < p ≤ t`). -/
def Acnt (P : Finset ℕ) (t : ℕ) : ℕ := (P.filter (fun p => 0 < p ∧ p ≤ t)).card

/-- **Members' reciprocal tail.** If `A(t) ≤ U √t` for natural `x0 ≤ t ≤ X`, `0 < x0`,
then `∑_{p ∈ P, x0 < p ≤ X} 1/p ≤ 2U/√x0`. -/
theorem member_tail (P : Finset ℕ) (U : ℝ) (x0 X : ℕ) (hx0 : 0 < x0) (hU : 0 ≤ U)
    (henv : ∀ t : ℕ, x0 ≤ t → t ≤ X → (Acnt P t : ℝ) ≤ U * √(t : ℝ)) :
    ∑ z ∈ (Ioc x0 X).filter (fun z => z ∈ P), ((z : ℝ))⁻¹ ≤ 2 * U / √(x0 : ℝ) := by
  classical
  set Q := (Ioc x0 X).filter (fun z => z ∈ P) with hQdef
  have hmemQ : ∀ q ∈ Q, x0 < q ∧ q ≤ X ∧ q ∈ P := by
    intro q hq
    simp only [hQdef, Finset.mem_filter, Finset.mem_Ioc] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  have hx0r : (0 : ℝ) < x0 := by exact_mod_cast hx0
  -- rank in Q ≤ A(q)
  have hrankA : ∀ q, (Q.filter (fun p => p ≤ q)).card ≤ Acnt P q := by
    intro q
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨h1, h2, h3⟩ := hmemQ p hp.1
    exact ⟨h3, by omega, hp.2⟩
  have hrank : ∀ q ∈ Q, ((Q.filter (fun p => p ≤ q)).card : ℝ) ≤ U * √(q : ℝ) := by
    intro q hq
    obtain ⟨h1, h2, _⟩ := hmemQ q hq
    calc ((Q.filter (fun p => p ≤ q)).card : ℝ) ≤ (Acnt P q : ℝ) := by
          exact_mod_cast hrankA q
      _ ≤ U * √(q : ℝ) := henv q h1.le h2
  by_cases hXx : X ≤ x0
  · have : Q = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro q hq; obtain ⟨h1, h2, _⟩ := hmemQ q hq; omega
    rw [this, Finset.sum_empty]; positivity
  push Not at hXx
  have hXr : (x0 : ℝ) ≤ X := by exact_mod_cast hXx.le
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le hx0r hXr
  have hcore := abel_core U x0 hU hx0r Q (fun q hq => by exact_mod_cast (hmemQ q hq).1)
    hrank (X : ℝ) (fun q hq => by exact_mod_cast (hmemQ q hq).2.1) hXr
  -- |Q| ≤ A(X) ≤ U √X
  have hcardQ : (Q.card : ℝ) ≤ U * √(X : ℝ) := by
    have h1 : Q.card ≤ Acnt P X := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hmemQ p hp
      simp only [Finset.mem_filter]; exact ⟨h3, by omega, h2⟩
    calc (Q.card : ℝ) ≤ (Acnt P X : ℝ) := by exact_mod_cast h1
      _ ≤ U * √(X : ℝ) := henv X hXx.le le_rfl
  have hsX : 0 < √(X : ℝ) := Real.sqrt_pos.mpr hXpos
  have hXsq : (X : ℝ) = √(X : ℝ) * √(X : ℝ) := (Real.mul_self_sqrt hXpos.le).symm
  have hdiv : (Q.card : ℝ) / X ≤ 2 * U / √(X : ℝ) := by
    rw [div_le_div_iff₀ hXpos hsX]
    nlinarith [hcardQ, mul_nonneg hU hsX.le]
  linarith

/-- **Lemma 2, full finite form.** With seed cutoff `s ≤ x0 ≤ X`, covering of all omitted
`z ∈ (s, X]`, and the envelope `A(t) ≤ U √t` on `[x0, X]`:
`log(X+1) - H_s - ∑_{p ∈ P ∩ (s, x0]} 1/p - 2U/√x0 + Rex ≤ W`. -/
theorem lemma2_full (P : Finset ℕ) (U : ℝ) (s x0 X : ℕ) (hsx : s ≤ x0) (hxX : x0 ≤ X)
    (hx0 : 0 < x0) (hU : 0 ≤ U)
    (hcov : ∀ z ∈ Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z)
    (henv : ∀ t : ℕ, x0 ≤ t → t ≤ X → (Acnt P t : ℝ) ≤ U * √(t : ℝ)) :
    Real.log ((X : ℝ) + 1) - (harmonic s : ℝ)
      - ∑ z ∈ (Ioc s x0).filter (fun z => z ∈ P), ((z : ℝ))⁻¹
      - 2 * U / √(x0 : ℝ) + Erdos271.WeightedCover.Rex P s X
      ≤ Erdos271.WeightedCover.W P := by
  classical
  have h2 := Erdos271.WeightedCover.lemma2_finite P s X (le_trans hsx hxX) hcov
  have ht := member_tail P U x0 X hx0 hU henv
  have hsplit : (Ioc s X).filter (fun z => z ∈ P)
      = (Ioc s x0).filter (fun z => z ∈ P) ∪ (Ioc x0 X).filter (fun z => z ∈ P) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases h : z ≤ x0
      · exact Or.inl ⟨⟨h1, h⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  have hdisj : Disjoint ((Ioc s x0).filter (fun z => z ∈ P)) ((Ioc x0 X).filter (fun z => z ∈ P)) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ioc] at h1 h2; omega
  rw [hsplit, Finset.sum_union hdisj] at h2
  linarith

end Erdos271.MemberTail
