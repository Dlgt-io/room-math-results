import Audit.General

/-!
# Stanley sequences `S(A)` (greedy definition) and the main theorem for them

`memb A m n`: greedy membership. For `n ≤ m` it is `n ∈ A`; for `n > m`, `n` is taken iff no
`a < b < n` already taken has `a + n = 2b`. **Fidelity:** membership is *frozen* on `[0, m]`, so
`StanleySeq A m` is the usual Stanley sequence `S(A)` only when `m = max A` (for `m > max A` it is a
broader frozen-prefix sequence; e.g. `A = {0}, m = 1` omits `1`). The main theorems hold for every
frozen-prefix sequence; the standard corollaries `stanley_std_*` (with `m = A.max' hne`) and
`two_seed_*` (`S(0,n)` as `StanleySeq {0,n} n`) are stated at the end.
-/

open Real Filter

namespace Erdos271.Stanley

def memb (A : Finset ℕ) (m : ℕ) (n : ℕ) : Bool :=
  if n ≤ m then decide (n ∈ A) else
    !((List.range n).attach.any fun ⟨b, _hb⟩ =>
      (List.range b).attach.any fun ⟨a, _ha⟩ =>
        memb A m a && memb A m b && (a + n == 2 * b))
termination_by n
decreasing_by
  · have := List.mem_range.mp ‹a ∈ List.range b›; have := List.mem_range.mp ‹b ∈ List.range n›
    omega
  · exact List.mem_range.mp ‹b ∈ List.range n›

/-- The Stanley sequence `S(A)` (greedy beyond `m`). -/
def StanleySeq (A : Finset ℕ) (m : ℕ) : Set ℕ := {n | memb A m n = true}

instance (A : Finset ℕ) (m : ℕ) : DecidablePred (· ∈ StanleySeq A m) := fun n =>
  inferInstanceAs (Decidable (memb A m n = true))

theorem memb_le (A : Finset ℕ) (m n : ℕ) (h : n ≤ m) : memb A m n = true ↔ n ∈ A := by
  rw [memb]; simp [h]

theorem memb_gt (A : Finset ℕ) (m n : ℕ) (h : m < n) :
    memb A m n = true ↔
      ¬ ∃ b, b < n ∧ ∃ a, a < b ∧ memb A m a = true ∧ memb A m b = true ∧ a + n = 2 * b := by
  rw [memb]
  simp only [show ¬ n ≤ m by omega, if_false, Bool.not_eq_true', List.any_eq_false,
    not_exists, not_and]
  constructor
  · intro H b hb a hab ha hb' he
    apply H ⟨b, List.mem_range.mpr hb⟩ (List.mem_attach _ _)
    rw [List.any_eq_true]
    exact ⟨⟨a, List.mem_range.mpr hab⟩, List.mem_attach _ _, by simp [ha, hb', he]⟩
  · intro H x _ hx
    rw [List.any_eq_true] at hx
    obtain ⟨y, _, hy⟩ := hx
    simp only [Bool.and_eq_true, beq_iff_eq] at hy
    exact H x.1 (List.mem_range.mp x.2) y.1 (List.mem_range.mp y.2) hy.1.1 hy.1.2 hy.2

variable (A : Finset ℕ) (m : ℕ) (hA : ∀ a ∈ A, a ≤ m)
  (hfreeA : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c → a + c ≠ 2 * b)
include hA hfreeA

theorem stanley_free : Erdos271.Final.ThreeAPFree (StanleySeq A m) := by
  intro a ha b hb c hc hab hbc he
  simp only [StanleySeq, Set.mem_setOf_eq] at ha hb hc
  by_cases hcm : c ≤ m
  · rw [memb_le A m a (by omega)] at ha
    rw [memb_le A m b (by omega)] at hb
    rw [memb_le A m c hcm] at hc
    exact hfreeA a ha b hb c hc hab hbc he
  · rw [memb_gt A m c (by omega)] at hc
    exact hc ⟨b, hbc, a, hab, ha, hb, he⟩

theorem stanley_greedy : ∀ z, m < z → z ∉ StanleySeq A m →
    ¬ Erdos271.Final.ThreeAPFree (insert z {n | n ∈ StanleySeq A m ∧ n < z}) := by
  intro z hz hzS hfree
  simp only [StanleySeq, Set.mem_setOf_eq] at hzS
  rw [memb_gt A m z hz] at hzS
  push Not at hzS
  obtain ⟨b, hbz, a, hab, ha, hb, he⟩ := hzS
  exact hfree a (Or.inr ⟨ha, by omega⟩) b (Or.inr ⟨hb, hbz⟩) z (Or.inl rfl) hab hbz he

theorem stanley_covering : ∀ z, m < z → z ∉ StanleySeq A m →
    ∃ a ∈ StanleySeq A m, ∃ b ∈ StanleySeq A m, a < b ∧ 2 * b - a = z :=
  Erdos271.Final.stanley_cover _ m (stanley_free A m hA hfreeA) (stanley_greedy A m hA hfreeA)

/-- **Main theorem for Stanley sequences.** `limsup F(x)/√x ≥ 1/√α`. -/
theorem stanley_limsup :
    ∀ U : ℝ, U < 1 / √(Real.log (1 + √2) / (2 * √2)) →
      ¬ ∀ᶠ x : ℝ in atTop, Erdos271.Side.AS (StanleySeq A m) x ≤ U * √x :=
  Erdos271.Final.erdos271_limsup_any _ m (stanley_covering A m hA hfreeA)

/-- **`a_k` form for Stanley sequences.** `liminf a_k/k² ≤ α`. -/
theorem stanley_ak :
    ∀ c : ℝ, Real.log (1 + √2) / (2 * √2) < c →
      ¬ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ Nat.nth (· ∈ StanleySeq A m) k :=
  Erdos271.Final.erdos271_ak_any _ m (stanley_covering A m hA hfreeA)

omit hA hfreeA in
/-- Standard Stanley sequence `S(A)`, `A` nonempty, 3-AP-free: cutoff exactly `max A`. -/
theorem stanley_std_limsup (A : Finset ℕ) (hne : A.Nonempty)
    (hfreeA : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c → a + c ≠ 2 * b) :
    ∀ U : ℝ, U < 1 / √(Real.log (1 + √2) / (2 * √2)) →
      ¬ ∀ᶠ x : ℝ in atTop, Erdos271.Side.AS (StanleySeq A (A.max' hne)) x ≤ U * √x :=
  stanley_limsup A (A.max' hne) (fun a ha => A.le_max' a ha) hfreeA

omit hA hfreeA in
theorem stanley_std_ak (A : Finset ℕ) (hne : A.Nonempty)
    (hfreeA : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a < b → b < c → a + c ≠ 2 * b) :
    ∀ c : ℝ, Real.log (1 + √2) / (2 * √2) < c →
      ¬ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ Nat.nth (· ∈ StanleySeq A (A.max' hne)) k :=
  stanley_ak A (A.max' hne) (fun a ha => A.le_max' a ha) hfreeA

omit hA hfreeA in
theorem two_seed_free (n : ℕ) : ∀ a ∈ ({0, n} : Finset ℕ), ∀ b ∈ ({0, n} : Finset ℕ),
    ∀ c ∈ ({0, n} : Finset ℕ), a < b → b < c → a + c ≠ 2 * b := by
  intro a ha b hb c hc hab hbc
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  omega

omit hA hfreeA in
/-- `S(0,n)` (`n = 0` gives `S(0)`): `limsup F/√x ≥ 1/√α`. -/
theorem two_seed_limsup (n : ℕ) :
    ∀ U : ℝ, U < 1 / √(Real.log (1 + √2) / (2 * √2)) →
      ¬ ∀ᶠ x : ℝ in atTop, Erdos271.Side.AS (StanleySeq ({0, n} : Finset ℕ) n) x ≤ U * √x :=
  stanley_limsup _ n (by intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha; omega)
    (two_seed_free n)

omit hA hfreeA in
theorem two_seed_ak (n : ℕ) :
    ∀ c : ℝ, Real.log (1 + √2) / (2 * √2) < c →
      ¬ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ Nat.nth (· ∈ StanleySeq ({0, n} : Finset ℕ) n) k :=
  stanley_ak _ n (by intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha; omega)
    (two_seed_free n)

end Erdos271.Stanley
