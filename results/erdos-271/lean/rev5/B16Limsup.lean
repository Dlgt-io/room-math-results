import B16

/-! # 17/6 as a `Filter.limsup` statement

Routine restatement of `Erdos271.B16.B16_main`/`B16_exists`: for the base-16 set,
`limsup_{x → ∞} A(x)/√x = 17/6` with `A(x) = #(S ∩ [1, ⌊x⌋])`. -/

namespace Erdos271.B16

open Filter

/-- Generic: a two-sided bound of the B16 form gives `limsup A(x)/√x = c`. -/
theorem limsup_eq_of_two_sided (A : ℝ → ℝ) (c : ℝ) (hA0 : ∀ x, 0 ≤ A x)
    (hup : ∀ x : ℝ, 1 ≤ x → A x + 1 ≤ c * Real.sqrt x)
    (hlow : ∀ U : ℝ, U < c → ∀ M : ℝ, ∃ x : ℝ, M ≤ x ∧ U * Real.sqrt x < A x) :
    limsup (fun x => A x / Real.sqrt x) atTop = c := by
  have hco : IsCoboundedUnder (· ≤ ·) atTop (fun x => A x / Real.sqrt x) :=
    isCoboundedUnder_le_of_le atTop (fun x => div_nonneg (hA0 x) (Real.sqrt_nonneg x))
  have hev : ∀ᶠ x in atTop, A x / Real.sqrt x ≤ c := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_iff₀ hs]; linarith [hup x hx]
  have hbd : IsBoundedUnder (· ≤ ·) atTop (fun x => A x / Real.sqrt x) := ⟨c, hev⟩
  apply le_antisymm (limsup_le_of_le hco hev)
  apply le_of_forall_lt
  intro d hd
  have hm : (d + c) / 2 < c := by linarith
  have hfr : ∃ᶠ x in atTop, (d + c) / 2 ≤ A x / Real.sqrt x := by
    rw [frequently_atTop]
    intro M
    obtain ⟨x, hMx, hx⟩ := hlow _ hm (max M 1)
    have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hMx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    refine ⟨x, le_trans (le_max_left _ _) hMx, ?_⟩
    rw [le_div_iff₀ hs]; exact hx.le
  have := le_limsup_of_frequently_le hfr hbd
  linarith

/-- Every set satisfying the base-16 recursion has `limsup A(x)/√x = 17/6`
(and is a weak AP3-covering beyond 88). -/
theorem B16_limsup (S : Set ℕ)
    (hS : ∀ n : Nat, Membership.mem S n ↔ (n = 0 ∨ n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 12 ∨ n = 14 ∨ n = 21 ∨ n = 23 ∨ n = 25 ∨ n = 28 ∨ (16 ≤ n ∧ (Nat.mod n 16 = 8 ∨ Nat.mod n 16 = 11 ∨ Nat.mod n 16 = 12 ∨ Nat.mod n 16 = 15) ∧ 0 < n / 16 ∧ Membership.mem S (n / 16)))) :
    (∀ z : Nat, 88 < z → ∃ a : Nat, ∃ b : Nat, a ∈ S ∧ b ∈ S ∧ 0 < a ∧ a < b ∧ b < z ∧ 2 * b - a = z) ∧
    limsup (fun x : ℝ => (Set.ncard (S ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) / Real.sqrt x) atTop = 17 / 6 := by
  obtain ⟨hc, hu, hl⟩ := B16_main S hS
  exact ⟨hc, limsup_eq_of_two_sided _ _ (fun x => Nat.cast_nonneg _) hu hl⟩

/-- The concrete set `S16` (= Claude's block set, `mem_iff_blocks`). -/
theorem S16_limsup :
    limsup (fun x : ℝ => (Set.ncard (S16 ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) / Real.sqrt x) atTop = 17 / 6 :=
  (B16_limsup S16 S16_char).2

end Erdos271.B16

#print axioms Erdos271.B16.B16_limsup
#print axioms Erdos271.B16.S16_limsup
