import LiminfCore

/-!
# Generic stacking: any certified static set gives a liminf bound

`StaticCert`: a positive set `S ∋ 1, 2` covering `[3, X]`, `X ≥ 3`. Then there is a strong
`AP₃`-covering set `A` (every `n ≥ 3` is `2b - a`, `0 < a < b < n`) with
`liminf |A ∩ [0,n]| / √n ≤ (|S| + 3) / √X`.
Stage `k`: `R_k = T_{k²}` (lift-and-fix), `Y_k = 4^{k²} X`, offsets `t_0 = 0`, `t_{k+1} = t_k + Y_k - 3`.
-/

open Finset Real

namespace Erdos271.Liminf

structure StaticCert where
  S : Finset ℕ
  X : ℕ
  hX : 3 ≤ X
  cov : Cov S 3 X
  h1 : 1 ∈ S
  h2 : 2 ∈ S
  pos : ∀ x ∈ S, 1 ≤ x

namespace StaticCert

variable (C : StaticCert)

def R (k : ℕ) : Finset ℕ := iter C.S (k * k)

def Y (k : ℕ) : ℕ := 4 ^ (k * k) * C.X

def t : ℕ → ℕ
  | 0 => 0
  | k + 1 => t k + C.Y k - 3

def Aset : Set ℕ := {m | ∃ k, ∃ r ∈ C.R k, m = r + C.t k}

theorem R_spec (k : ℕ) :
    Cov (C.R k) 3 (C.Y k) ∧ (∀ x ∈ C.R k, 1 ≤ x) ∧
      (C.R k).card + 3 = 2 ^ (k * k) * (C.S.card + 3) := by
  obtain ⟨h1, -, -, h4, h5⟩ := iter_spec C.S C.X C.hX C.cov C.h1 C.h2 C.pos (k * k)
  exact ⟨h1, h4, h5⟩

theorem Y_ge (k : ℕ) : 3 ≤ C.Y k := le_trans C.hX (Nat.le_mul_of_pos_left _ (by positivity))

theorem Y_ge_succ (k : ℕ) : 12 ≤ C.Y (k + 1) := by
  have h : 4 ≤ 4 ^ ((k + 1) * (k + 1)) := by
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ ((k + 1) * (k + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have := C.hX
  unfold Y; nlinarith

theorem le_Y (n : ℕ) : n ≤ C.Y n := by
  have h1 : n < 4 ^ n := Nat.lt_pow_self (by norm_num)
  have h2 : 4 ^ n ≤ 4 ^ (n * n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self n)
  have h3 : 4 ^ (n * n) ≤ 4 ^ (n * n) * C.X := Nat.le_mul_of_pos_right _ (by have := C.hX; omega)
  unfold Y; omega

theorem t_succ (k : ℕ) : C.t (k + 1) + 3 = C.t k + C.Y k := by
  have := C.Y_ge k
  simp only [t]; omega

theorem t_mono : Monotone C.t :=
  monotone_nat_of_le_succ fun k => by have := C.t_succ k; have := C.Y_ge k; omega

theorem stage_cov (k n : ℕ) (h1 : C.t k + 3 ≤ n) (h2 : n ≤ C.t k + C.Y k) :
    ∃ a ∈ C.Aset, ∃ b ∈ C.Aset, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
  obtain ⟨a, ha, b, hb, ha1, hab, he⟩ := (C.R_spec k).1 (n - C.t k) (by omega) (by omega)
  exact ⟨a + C.t k, ⟨k, a, ha, rfl⟩, b + C.t k, ⟨k, b, hb, rfl⟩, by omega, by omega, by omega,
    by omega⟩

theorem covering :
    ∀ n, 3 ≤ n → ∃ a ∈ C.Aset, ∃ b ∈ C.Aset, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b := by
  intro n hn
  classical
  have hex : ∃ k, n ≤ C.t k + C.Y k := ⟨n, by have := C.le_Y n; omega⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, n ≤ C.t k + C.Y k ∧ ∀ i < k, ¬ n ≤ C.t i + C.Y i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  cases k with
  | zero => exact C.stage_cov 0 n (by simp only [t]; omega) hk
  | succ p =>
    exact C.stage_cov (p + 1) n (by have := hmin p (by omega); have := C.t_succ p; omega) hk

def F (k : ℕ) : Finset ℕ :=
  ((range (k + 1)).biUnion fun i => (C.R i).image (· + C.t i)) ∪
    ({1, 2, 3} : Finset ℕ).image (· + C.t (k + 1))

theorem sub_F (k : ℕ) : C.Aset ∩ Set.Iic (C.t k + C.Y k) ⊆ ↑(C.F k) := by
  rintro m ⟨⟨i, r, hr, rfl⟩, hm⟩
  simp only [Set.mem_Iic] at hm
  rw [Finset.mem_coe]
  have hr1 := (C.R_spec i).2.1 r hr
  rcases lt_trichotomy i (k + 1) with h | h | h
  · refine Finset.mem_union_left _ ?_
    rw [mem_biUnion]
    exact ⟨i, mem_range.2 h, mem_image.2 ⟨r, hr, rfl⟩⟩
  · subst h
    refine Finset.mem_union_right _ ?_
    have := C.t_succ k
    rw [mem_image]
    refine ⟨r, ?_, rfl⟩
    simp only [mem_insert, mem_singleton]
    omega
  · exfalso
    have hm2 : C.t (k + 1 + 1) ≤ C.t i := C.t_mono (by omega)
    have := C.t_succ (k + 1)
    have := C.t_succ k
    have := C.Y_ge_succ k
    omega

theorem card_F (k : ℕ) : (C.F k).card ≤ (∑ i ∈ range (k + 1), (C.R i).card) + 3 := by
  calc (C.F k).card ≤ ((range (k + 1)).biUnion fun i => (C.R i).image (· + C.t i)).card +
        (({1, 2, 3} : Finset ℕ).image (· + C.t (k + 1))).card := card_union_le _ _
    _ ≤ (∑ i ∈ range (k + 1), (C.R i).card) + 3 := by
        apply add_le_add
        · exact card_biUnion_le.trans (sum_le_sum fun i _ => card_image_le)
        · exact card_image_le.trans (by decide)

noncomputable def cnt (n : ℕ) : ℕ := (C.Aset ∩ Set.Iic n).ncard

theorem cnt_le (k : ℕ) : C.cnt (C.t k + C.Y k) ≤ (C.F k).card := by
  unfold cnt
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (C.sub_F k) (Finset.finite_toSet _)

theorem geom (m : ℕ) : ∑ i ∈ range (m + 1), 2 ^ (i * i) < 2 ^ (m * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have h1 : 2 ^ (m * m + 1) ≤ 2 ^ ((m + 1) * (m + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ ((m + 1) * (m + 1) + 1) = 2 * 2 ^ ((m + 1) * (m + 1)) := by ring
    omega

/-- Earlier stages are `o(√Y)`: `A(x_{m+1}) ≤ (K+3)·2^{(m+1)²} + (K+6)·2^{m²+1}`. -/
theorem cnt_bound (m : ℕ) :
    C.cnt (C.t (m + 1) + C.Y (m + 1)) ≤
      (C.S.card + 3) * 2 ^ ((m + 1) * (m + 1)) + (C.S.card + 6) * 2 ^ (m * m + 1) := by
  have h1 := C.cnt_le (m + 1)
  have h2 := C.card_F (m + 1)
  have h3 : ∑ i ∈ range (m + 1 + 1), (C.R i).card ≤
      ∑ i ∈ range (m + 1 + 1), (C.S.card + 3) * 2 ^ (i * i) :=
    sum_le_sum fun i _ => by have := (C.R_spec i).2.2; rw [mul_comm]; omega
  have h4 : ∑ i ∈ range (m + 1 + 1), (C.S.card + 3) * 2 ^ (i * i) =
      (C.S.card + 3) * (∑ i ∈ range (m + 1), 2 ^ (i * i)) +
        (C.S.card + 3) * 2 ^ ((m + 1) * (m + 1)) := by
    rw [sum_range_succ, mul_sum]
  have h5 := geom m
  have h6 : 1 ≤ 2 ^ (m * m + 1) := Nat.one_le_two_pow
  have h7 : (C.S.card + 3) * (∑ i ∈ range (m + 1), 2 ^ (i * i)) + 3 ≤
      (C.S.card + 6) * 2 ^ (m * m + 1) := by nlinarith
  omega

theorem pow_split (m : ℕ) : (2 : ℝ) ^ ((m + 1) * (m + 1)) = 2 ^ (m * m + 1) * 4 ^ m := by
  rw [show (m + 1) * (m + 1) = (m * m + 1) + 2 * m by ring, pow_add, pow_mul]
  norm_num

/-- **Generic theorem.** -/
theorem liminf_of_cert :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
        ((A ∩ Set.Iic n).ncard : ℝ) ≤ ((C.S.card + 3 : ℝ) / √(C.X : ℝ) + ε) * √(n : ℝ) := by
  refine ⟨C.Aset, C.covering, ?_⟩
  intro ε hε N
  set K : ℝ := (C.S.card : ℝ) with hK
  have hX3 : (3 : ℝ) ≤ C.X := by exact_mod_cast C.hX
  set s : ℝ := √(C.X : ℝ) with hs
  have hs2 : s ^ 2 = C.X := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 ≤ s := by nlinarith
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℕ, (K + 6) / ε < 4 ^ m0 := pow_unbounded_of_one_lt _ (by norm_num)
  set m := max m0 N with hm
  refine ⟨C.t (m + 1) + C.Y (m + 1), ?_, ?_⟩
  · have := C.le_Y (m + 1); have := le_max_right m0 N; omega
  · set P : ℝ := (2 : ℝ) ^ ((m + 1) * (m + 1)) with hP
    set Q : ℝ := (2 : ℝ) ^ (m * m + 1) with hQ
    have hc : ((C.cnt (C.t (m + 1) + C.Y (m + 1)) : ℕ) : ℝ) ≤ (K + 3) * P + (K + 6) * Q := by
      have := C.cnt_bound m
      rw [hP, hQ, hK]; exact_mod_cast this
    have hPQ : P = Q * 4 ^ m := pow_split m
    have hQ0 : 0 < Q := by positivity
    have hK0 : 0 ≤ K := by positivity
    have h4 : (4 : ℝ) ^ m0 ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    have h56 : K + 6 < ε * 4 ^ m := by
      have := (div_lt_iff₀ hε).1 hm0
      nlinarith
    have hQP : (K + 6) * Q ≤ ε * P := by rw [hPQ]; nlinarith
    have hx : (C.X : ℝ) * P ^ 2 ≤ ((C.t (m + 1) + C.Y (m + 1) : ℕ) : ℝ) := by
      have hn : C.X * (2 ^ ((m + 1) * (m + 1))) ^ 2 ≤ C.t (m + 1) + C.Y (m + 1) := by
        have e : (2 ^ ((m + 1) * (m + 1))) ^ 2 = 4 ^ ((m + 1) * (m + 1)) := by
          rw [← pow_mul, mul_comm _ 2, pow_mul]; norm_num
        rw [e]; unfold Y; rw [mul_comm]; omega
      rw [hP]; exact_mod_cast hn
    have hsq : s * P ≤ √((C.t (m + 1) + C.Y (m + 1) : ℕ) : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith
    have hP0 : 0 < P := by positivity
    have key : (K + 3) / s * (s * P) = (K + 3) * P := by field_simp
    calc ((C.Aset ∩ Set.Iic (C.t (m + 1) + C.Y (m + 1))).ncard : ℝ)
        = ((C.cnt (C.t (m + 1) + C.Y (m + 1)) : ℕ) : ℝ) := rfl
      _ ≤ (K + 3) * P + ε * P := by linarith
      _ ≤ ((K + 3) / s + ε) * (s * P) := by
          rw [add_mul ((K + 3) / s) ε, key]
          nlinarith [mul_nonneg (mul_nonneg hε.le hP0.le) (sub_nonneg.2 hs1)]
      _ ≤ ((K + 3) / s + ε) * √((C.t (m + 1) + C.Y (m + 1) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

end StaticCert

end Erdos271.Liminf
