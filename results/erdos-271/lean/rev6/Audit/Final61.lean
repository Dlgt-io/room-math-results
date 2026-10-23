import Audit.Final

/-!
# (6.1) for weak AP3-covering sets, and the unconditional end-to-end theorem

`h61_holds` proves the obligation `H61` of `Final.lean` from the compiled pieces:
`lemma2_full` (Lemma 2), `W_eq_weightedPairs` (ℕ ↔ ℝ), `finite_weighted_integral_identity`
(Lemma 3, ChatGPT), `log_window_bound` (log substitution + Lemma 4), and the side lemmas.
-/

open MeasureTheory Set Real Filter
open Erdos271.Alpha Erdos271.Side Erdos271.Final Erdos271.FiniteIntegrals

namespace Erdos271.Final

variable (S : Set ℕ) [DecidablePred (· ∈ S)]

theorem h61_holds (h0 : 0 ∈ S) (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) : H61 S := by
  intro U hU hUC ⟨x0, hx01, henv⟩
  have hU95 : U < 9 / 5 := lt_trans hUC Cstar_lt
  set y0 : ℕ := max x0 s with hy0
  have hy0x : x0 ≤ y0 := le_max_left _ _
  have hsy : s ≤ y0 := le_max_right _ _
  have hy01 : 1 ≤ y0 := le_trans hx01 hy0x
  have hy0r : (1 : ℝ) ≤ y0 := by exact_mod_cast hy01
  have henv' : ∀ x : ℝ, (y0 : ℝ) ≤ x → (7 / 5) * √x ≤ AS S x ∧ AS S x ≤ U * √x :=
    fun x hx => henv x (le_trans (by exact_mod_cast hy0x) hx)
  -- constants independent of X
  set c1 : ℝ := ∑ z ∈ (Finset.Ioc s y0).filter (fun z => z ∈ S), ((z : ℝ))⁻¹
  set c2 : ℝ := ∫ x in Ioo 1 (y0 : ℝ), AS S x ^ 2 / x ^ 2
  refine ⟨(harmonic s : ℝ) + c1 + 2 * U / √(y0 : ℝ) + (3 / 2) * c2
      - α * U ^ 2 * Real.log y0 + 8 * U ^ 2 + U ^ 2 / 2, y0, fun X hX => ?_⟩
  set P := Pfin S X with hPdef
  have hXr : (y0 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) < X := by linarith
  -- (a) Lemma 2
  have hcovP : ∀ z ∈ Finset.Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z := by
    intro z hz hzP
    rw [Finset.mem_Ioc] at hz
    have hzS : z ∉ S := fun h => hzP (by
      simp only [hPdef, Pfin, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, h⟩)
    obtain ⟨a, ha, b, hb, hab, he⟩ := hcov z hz.1 hzS
    refine ⟨a, ?_, b, ?_, hab, he⟩ <;>
      simp only [hPdef, Pfin, Finset.mem_filter, Finset.mem_range] <;>
      refine ⟨by omega, by assumption⟩
  have henvN : ∀ t : ℕ, y0 ≤ t → t ≤ X →
      (Erdos271.MemberTail.Acnt P t : ℝ) ≤ U * √(t : ℝ) := by
    intro t h1 h2
    rw [hPdef, Acnt_Pfin S h2]
    exact (henv' t (by exact_mod_cast h1)).2
  have L2 := Erdos271.MemberTail.lemma2_full P U s y0 X hsy hX (by omega) hU hcovP henvN
  rw [hPdef, members_indep S hX] at L2
  -- (b) bridge
  have h0P : 0 ∈ P := by
    simp only [hPdef, Pfin, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, h0⟩
  have hW := Erdos271.Glue.W_eq_weightedPairs P h0P
  -- (c) finite identity
  have hPX : ∀ p ∈ P, p ≤ X := by
    intro p hp
    simp only [hPdef, Pfin, Finset.mem_filter, Finset.mem_range] at hp; omega
  have hPr := Erdos271.Glue.Pr_mem P hPX
  obtain ⟨_, _, hId, _, hE⟩ := finite_weighted_integral_identity (Erdos271.Glue.Pr P) X hX0
    (fun p hp => ⟨by linarith [(hPr p hp).1], (hPr p hp).2⟩)
  -- (d) log window bound
  have henvR : ∀ x ∈ Icc (y0 : ℝ) X, (7 / 5) * √x ≤ Acount (Erdos271.Glue.Pr P) x ∧
      Acount (Erdos271.Glue.Pr P) x ≤ U * √x := by
    intro x hx
    rw [hPdef, Acount_Pfin S (by linarith [hx.1]) hx.2]
    exact henv' x hx.1
  have LW := Erdos271.Glue.log_window_bound (Erdos271.Glue.Pr P) (fun p hp => (hPr p hp).1)
    hy0r hXr hU henvR
  simp only at LW
  obtain ⟨hη0, hη2, hmain⟩ := LW
  rw [beta_eq, hPdef, I0_indep S hXr] at hmain
  -- D ≥ 0 and κ > 0
  have hlog : Real.log y0 ≤ Real.log X := Real.log_le_log (by linarith) hXr
  have hD := D_nonneg (h := hfun (Acount (Erdos271.Glue.Pr (Pfin S X)))) hlog
    (fun t ht => (Erdos271.Glue.hfun_env (Erdos271.Glue.Pr (Pfin S X)) (by linarith) hXr
      (by rw [← hPdef]; exact henvR) t ht).2)
  have hκ := kappa_pos hU hU95
  have hκD := mul_nonneg hκ.le hD
  -- (e) E ≤ U²/2
  have hcard : ((Erdos271.Glue.Pr P).card : ℝ) ≤ U * √(X : ℝ) := by
    rw [hPdef, Pfin_card S]; exact (henv' X hXr).2
  have hE2 := E_le (Erdos271.Glue.Pr P) hX0 hcard hE
  -- (f) Rex ≥ 0
  have hR : 0 ≤ Erdos271.WeightedCover.Rex (Pfin S X) s X :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg _)))
  -- (g) log X ≤ log (X+1)
  have hlX : Real.log X ≤ Real.log ((X : ℝ) + 1) := Real.log_le_log hX0 (by linarith)
  have hη : 4 * U ^ 2 * (∫ v in Ioi 0, v * Kker v) ≤ 8 * U ^ 2 := by nlinarith [sq_nonneg U]
  rw [hPdef] at hW hId hE2
  linarith

/-- **Main theorem (Lean, unconditional).** For every `S ⊆ ℕ` with `0 ∈ S` that is weakly
AP3-covering beyond `s` (every `z > s` not in `S` is `2b - a` with `a < b` in `S`), no
`U < C_* = 1/√α`, `α = log(1+√2)/(2√2)`, is an eventual envelope: `limsup A(x)/√x ≥ C_*`. -/
theorem erdos271_limsup (h0 : 0 ∈ S) (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ U : ℝ, U < 1 / √(Real.log (1 + √2) / (2 * √2)) →
      ¬ ∀ᶠ x : ℝ in atTop, AS S x ≤ U * √x :=
  erdos271_limsup_of S s hcov (h61_holds S h0 s hcov)

/-- Limsup form (when `A(x)/√x` is bounded above; otherwise the limsup is `+∞`). -/
theorem erdos271_limsup_ge (h0 : 0 ∈ S) (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z)
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun x => AS S x / √x)) :
    1 / √(Real.log (1 + √2) / (2 * √2)) ≤ limsup (fun x => AS S x / √x) atTop :=
  erdos271_limsup_ge_of S s hcov (h61_holds S h0 s hcov) hb

end Erdos271.Final
