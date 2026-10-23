import Mathlib

/-!
# Finite weighted covering inequality and harmonic lower bound (Lemma 2, finite core)

`P` is a finite set of naturals (in the application `P = S ∩ [0, X]`).
`W P = ∑_{a<b in P} 1/(2b-a)`, `r P z = #{a<b in P : 2b-a = z}`,
`Rex P s X = ∑_{s<z≤X} (r z - 1)_+ / z`.
-/

open Finset

namespace Erdos271.WeightedCover

/-- Ordered pairs `a < b` from `P`. -/
def pairs (P : Finset ℕ) : Finset (ℕ × ℕ) := (P ×ˢ P).filter (fun q => q.1 < q.2)

/-- The covered target `2b - a`. -/
def tgt (q : ℕ × ℕ) : ℕ := 2 * q.2 - q.1

/-- Weighted pair sum. -/
noncomputable def W (P : Finset ℕ) : ℝ := ∑ q ∈ pairs P, ((tgt q : ℕ) : ℝ)⁻¹

/-- Representation count. -/
def r (P : Finset ℕ) (z : ℕ) : ℕ := ((pairs P).filter (fun q => tgt q = z)).card

/-- Weighted redundant coverage `∑_{s<z≤X} (r z - 1)_+ / z`. -/
noncomputable def Rex (P : Finset ℕ) (s X : ℕ) : ℝ :=
  ∑ z ∈ Ioc s X, ((r P z - 1 : ℕ) : ℝ) * (z : ℝ)⁻¹

/-- Fibre bound: `∑_{s<z≤X} r(z)/z ≤ W`. -/
theorem fiber_le_W (P : Finset ℕ) (s X : ℕ) :
    ∑ z ∈ Ioc s X, (r P z : ℝ) * (z : ℝ)⁻¹ ≤ W P := by
  classical
  have hfib : ∑ z ∈ Ioc s X, (r P z : ℝ) * (z : ℝ)⁻¹
      = ∑ q ∈ (pairs P).filter (fun q => tgt q ∈ Ioc s X), ((tgt q : ℕ) : ℝ)⁻¹ := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := tgt) (t := Ioc s X)
      (fun q hq => (Finset.mem_filter.mp hq).2)]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [Finset.filter_filter]
    have hset : (pairs P).filter (fun q => tgt q ∈ Ioc s X ∧ tgt q = z)
        = (pairs P).filter (fun q => tgt q = z) := by
      refine Finset.filter_congr (fun q _ => ?_)
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hz, h⟩
    rw [hset]
    have : ∑ q ∈ (pairs P).filter (fun q => tgt q = z), ((tgt q : ℕ) : ℝ)⁻¹
        = ∑ q ∈ (pairs P).filter (fun q => tgt q = z), (z : ℝ)⁻¹ :=
      Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2])
    rw [this, Finset.sum_const, nsmul_eq_mul, r]
  rw [hfib, W]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun q _ _ => by positivity)

/-- A covering witness gives `r z ≥ 1`. -/
theorem one_le_r_of_witness {P : Finset ℕ} {z a b : ℕ} (ha : a ∈ P) (hb : b ∈ P)
    (hab : a < b) (hz : 2 * b - a = z) : 1 ≤ r P z := by
  unfold r
  apply Finset.card_pos.mpr
  exact ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, hz⟩⟩

/-- **Finite weighted covering inequality.** If every omitted `z ∈ (s, X]` is covered
(`2b - a = z` with `a < b` in `P`), then
`∑_{omitted z} 1/z + Rex ≤ W`. -/
theorem weighted_covering (P : Finset ℕ) (s X : ℕ)
    (hcov : ∀ z ∈ Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z) :
    ∑ z ∈ (Ioc s X).filter (fun z => z ∉ P), (z : ℝ)⁻¹ + Rex P s X ≤ W P := by
  classical
  refine le_trans ?_ (fiber_le_W P s X)
  rw [Finset.sum_filter, Rex, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun z hz => ?_)
  have hzinv : (0 : ℝ) ≤ (z : ℝ)⁻¹ := by positivity
  by_cases hP : z ∈ P
  · simp only [hP, not_true_eq_false, ite_false, zero_add]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) hzinv
  · simp only [hP, not_false_eq_true, ite_true]
    obtain ⟨a, ha, b, hb, hab, hz'⟩ := hcov z hz hP
    have h1 := one_le_r_of_witness ha hb hab hz'
    have : ((r P z - 1 : ℕ) : ℝ) = (r P z : ℝ) - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_one]
    rw [this]; ring_nf; exact le_refl _

/-- **Harmonic lower bound** for the window `(s, X]`. -/
theorem harmonic_window (s X : ℕ) (hsX : s ≤ X) :
    Real.log ((X : ℝ) + 1) - (harmonic s : ℝ) ≤ ∑ z ∈ Ioc s X, (z : ℝ)⁻¹ := by
  have hsplit : (harmonic X : ℝ) = (harmonic s : ℝ) + ∑ z ∈ Ioc s X, (z : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    have hI : ∀ n : ℕ, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hI, hI, Finset.sum_Ioc_consecutive _ (Nat.zero_le s) hsX]
  have h := log_add_one_le_harmonic X
  push_cast at h
  linarith

/-- **Lemma 2, finite core.** Under the covering hypothesis,
`log(X+1) - H_s - ∑_{z ∈ P, s<z≤X} 1/z + Rex ≤ W`. -/
theorem lemma2_finite (P : Finset ℕ) (s X : ℕ) (hsX : s ≤ X)
    (hcov : ∀ z ∈ Ioc s X, z ∉ P → ∃ a ∈ P, ∃ b ∈ P, a < b ∧ 2 * b - a = z) :
    Real.log ((X : ℝ) + 1) - (harmonic s : ℝ)
      - ∑ z ∈ (Ioc s X).filter (fun z => z ∈ P), (z : ℝ)⁻¹ + Rex P s X ≤ W P := by
  classical
  have h1 := weighted_covering P s X hcov
  have h2 := harmonic_window s X hsX
  have h3 := Finset.sum_filter_add_sum_filter_not (Ioc s X) (fun z => z ∈ P)
    (fun z => (z : ℝ)⁻¹)
  linarith

end Erdos271.WeightedCover

#print axioms Erdos271.WeightedCover.fiber_le_W
#print axioms Erdos271.WeightedCover.weighted_covering
#print axioms Erdos271.WeightedCover.harmonic_window
#print axioms Erdos271.WeightedCover.lemma2_finite
