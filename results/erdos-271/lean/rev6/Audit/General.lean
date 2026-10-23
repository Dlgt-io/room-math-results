import Audit.AkForm

/-!
# Removing the assumption `0 ∈ S`; Stanley sequences satisfy the covering hypothesis

* `cover_insert0`: if `S` is weakly AP3-covering beyond `s`, so is `S ∪ {0}` (ChatGPT's
  observation, #119: enlarge rather than translate). `AS_insert0`: the positive counting
  function is unchanged.
* **`erdos271_limsup_any`**, `erdos271_limsup_ge_any`: the main theorem for every `S ⊆ ℕ`.
* **`erdos271_ak_any`**: `liminf a_k/k² ≤ α` for every such `S` (no `0 ∈ S`), with
  `a_k = Nat.nth S k`.
* **`stanley_cover`**: if `S` is 3-AP-free and *greedy beyond `s`* (every `z > s` not in `S`
  creates a 3-AP when added to `S ∩ [0, z)`), then `S` is weakly AP3-covering beyond `s`.
  A Stanley sequence `S(A)` is greedy beyond `max A` by definition.
-/

open Real Filter Finset
open Erdos271.Alpha Erdos271.Side

namespace Erdos271.Final

section
variable (S : Set ℕ) [DecidablePred (· ∈ S)]

/-- `S ∪ {0}`. -/
def S0 : Set ℕ := insert 0 S

instance : DecidablePred (· ∈ S0 S) := fun n =>
  (inferInstance : Decidable (n = 0 ∨ n ∈ S))

theorem cover_insert0 (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ z, s < z → z ∉ S0 S → ∃ a ∈ S0 S, ∃ b ∈ S0 S, a < b ∧ 2 * b - a = z := by
  intro z hz hzS
  have : z ∉ S := fun h => hzS (Or.inr h)
  obtain ⟨a, ha, b, hb, hab, he⟩ := hcov z hz this
  exact ⟨a, Or.inr ha, b, Or.inr hb, hab, he⟩

theorem AS_insert0 (x : ℝ) : AS (S0 S) x = AS S x := by
  unfold AS
  congr 2
  apply Finset.filter_congr
  intro n _
  simp only [S0, Set.mem_insert_iff]
  constructor
  · rintro ⟨h | h, hp⟩
    · omega
    · exact ⟨h, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨Or.inr h, hp⟩

/-- **Main theorem for every `S ⊆ ℕ`** (no `0 ∈ S`). -/
theorem erdos271_limsup_any (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ U : ℝ, U < 1 / √(Real.log (1 + √2) / (2 * √2)) →
      ¬ ∀ᶠ x : ℝ in atTop, AS S x ≤ U * √x := by
  intro U hU hev
  refine erdos271_limsup (S0 S) (Set.mem_insert 0 S) s (cover_insert0 S s hcov) U hU ?_
  filter_upwards [hev] with x hx
  rw [AS_insert0]; exact hx

theorem erdos271_limsup_ge_any (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z)
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun x => AS S x / √x)) :
    1 / √(Real.log (1 + √2) / (2 * √2)) ≤ limsup (fun x => AS S x / √x) atTop := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, h1, h2⟩ := exists_between hlt
  exact erdos271_limsup_any S s hcov U h2 (env_of_limsup S hb h1)

/-- `a_{A(x) - 1} ≤ x` whenever `A(x) ≥ 1` (no `0 ∈ S` needed). -/
theorem nth_pred_le (hinf : S.Infinite) {x : ℝ} (hx : 0 ≤ x)
    (hn : 1 ≤ ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card) :
    (Nat.nth (· ∈ S) (((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card - 1) : ℝ)
      ≤ x := by
  have hsub : ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card
      ≤ Nat.count (· ∈ S) (⌊x⌋₊ + 1) := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro n hn; simp only [Finset.mem_filter] at hn ⊢; exact ⟨hn.1, hn.2.1⟩
  have h := (Nat.lt_nth_iff_count_lt (p := (· ∈ S)) hinf
    (a := ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card - 1)
    (b := ⌊x⌋₊ + 1)).mp (by omega)
  have h' : Nat.nth (· ∈ S)
      (((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card - 1) ≤ ⌊x⌋₊ := by omega
  calc (Nat.nth (· ∈ S) _ : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h'
    _ ≤ x := Nat.floor_le hx

/-- **`a_k` form for every `S ⊆ ℕ`**: `liminf a_k/k² ≤ α`. -/
theorem erdos271_ak_any (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ c : ℝ, Real.log (1 + √2) / (2 * √2) < c →
      ¬ ∀ᶠ k : ℕ in atTop, c * (k : ℝ) ^ 2 ≤ Nat.nth (· ∈ S) k := by
  intro c hc hev
  have hinf := infinite_of_cover S s hcov
  have ha := alpha_pos
  change α < c at hc
  have hc0 : 0 < c := lt_trans ha hc
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  have hsc : √α < √c := Real.sqrt_lt_sqrt ha.le hc
  have hsa := Real.sqrt_pos.mpr ha
  have hscp := Real.sqrt_pos.mpr hc0
  set U : ℝ := (1 / √c + 1 / √α) / 2 with hUdef
  have h1 : 1 / √c < 1 / √α := one_div_lt_one_div_of_lt hsa hsc
  have hUlt : U < 1 / √α := by rw [hUdef]; linarith
  have hUgt : 1 / √c < U := by rw [hUdef]; linarith
  have hUpos : 0 < U := lt_trans (by positivity) hUgt
  set δ : ℝ := U - 1 / √c with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  apply erdos271_limsup_any S s hcov U hUlt
  filter_upwards [eventually_ge_atTop ((((K : ℝ) + 1) / U) ^ 2),
    eventually_ge_atTop ((1 / δ) ^ 2)] with x hx hx'
  have hx0 : 0 ≤ x := le_trans (sq_nonneg _) hx
  set n := ((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card with hn
  show (n : ℝ) ≤ U * √x
  have hsx : ((K : ℝ) + 1) / U ≤ √x := Real.le_sqrt_of_sq_le hx
  have hsx' : 1 / δ ≤ √x := Real.le_sqrt_of_sq_le hx'
  by_cases hnK : n ≤ K + 1
  · have : (n : ℝ) ≤ K + 1 := by exact_mod_cast hnK
    have : (K : ℝ) + 1 ≤ U * √x := by rwa [div_le_iff₀ hUpos, mul_comm] at hsx
    linarith
  · push Not at hnK
    have hak := hK (n - 1) (by omega)
    have hle := nth_pred_le S hinf hx0 (by rw [← hn]; omega)
    rw [← hn] at hle
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at hak
    have hcn : c * ((n : ℝ) - 1) ^ 2 ≤ x := le_trans hak hle
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    have hq : (√c * ((n : ℝ) - 1)) ^ 2 ≤ (√x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc0.le, Real.sq_sqrt hx0]; exact hcn
    have hq' : √c * ((n : ℝ) - 1) ≤ √x :=
      (pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg _) two_ne_zero).mp hq
    -- n - 1 ≤ √x / √c and 1 ≤ δ √x
    have hA : (n : ℝ) - 1 ≤ 1 / √c * √x := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hscp]; linarith
    have hB : 1 ≤ δ * √x := by
      rw [div_le_iff₀ hδ0] at hsx'; linarith
    have : U * √x = 1 / √c * √x + δ * √x := by rw [hδ]; ring
    linarith

end

/-- 3-AP-freeness. -/
def ThreeAPFree (T : Set ℕ) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, a < b → b < c → a + c ≠ 2 * b

/-- **Stanley sequences are weakly AP3-covering.** If `S` is 3-AP-free and greedy beyond
`s` (adding any `z > s`, `z ∉ S`, to `S ∩ [0, z)` creates a 3-AP), then every such `z` is
`2b - a` with `a < b` in `S`. -/
theorem stanley_cover (S : Set ℕ) (s : ℕ) (hfree : ThreeAPFree S)
    (hgreedy : ∀ z, s < z → z ∉ S → ¬ ThreeAPFree (insert z {n | n ∈ S ∧ n < z})) :
    ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z := by
  intro z hz hzS
  have h := hgreedy z hz hzS
  unfold ThreeAPFree at h
  push Not at h
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, he⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_setOf_eq] at ha hb hc
  -- z must be the top element c
  rcases hc with rfl | ⟨hcS, hcz⟩
  · rcases hb with rfl | ⟨hbS, _⟩
    · omega
    rcases ha with rfl | ⟨haS, _⟩
    · omega
    exact ⟨a, haS, b, hbS, hab, by omega⟩
  · rcases hb with rfl | ⟨_, hbz⟩
    · omega
    rcases ha with rfl | ⟨_, haz⟩
    · omega
    exact absurd he (hfree a (by tauto) b (by tauto) c hcS hab hbc)

end Erdos271.Final
