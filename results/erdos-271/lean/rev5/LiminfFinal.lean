import LiminfGen
import LiminfCert3072
import LiminfCert49152

/-!
# Liminf bounds from certified static sets

* `liminf_construction_1889`: `53√3/48 → 419√3/384 ≈ 1.88992` (Claude, `S₄₉₁₅₂`, 416 elements).
* `liminf_construction_1894`: `35√3/32 ≈ 1.89443` (`S₃₀₇₂`, 102 elements).
* `liminf_construction_1912`: `53√3/48 ≈ 1.91247` (`S₇₆₈`, 50 elements), as an instance of the
  generic theorem (the original direct proof is `Liminf.lean`).
-/

open Real

namespace Erdos271.Liminf

def cert768 : StaticCert :=
  ⟨S768, 768, by norm_num, S768_cov, S768_small.1, S768_small.2.1, S768_pos⟩

def cert3072 : StaticCert :=
  ⟨bitset B3072 3072, 3072, by norm_num, S3072_cov, S3072_small.1, S3072_small.2, S3072_pos⟩

def cert49152 : StaticCert :=
  ⟨bitset B49152 49152, 49152, by norm_num, S49152_cov, S49152_small.1, S49152_small.2,
    S49152_pos⟩

theorem div_sqrt (a b : ℝ) (hb : 0 < b) : a / √(b ^ 2 * 3) = a * √3 / (3 * b) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hb.le]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have : 0 < √3 := by positivity
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(a * b)) * h3

/-- Transfer the generic bound to an explicit constant. -/
theorem of_cert (C : StaticCert) (c : ℝ) (hc : ((C.S.card + 3 : ℝ)) / √(C.X : ℝ) = c) :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N, ((A ∩ Set.Iic n).ncard : ℝ) ≤ (c + ε) * √(n : ℝ) := by
  obtain ⟨A, hA, hB⟩ := C.liminf_of_cert
  exact ⟨A, hA, fun ε hε N => by rw [← hc]; exact hB ε hε N⟩

/-- **Claude's 1.88992 bound, formalised.** -/
theorem liminf_construction_1889 :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
        ((A ∩ Set.Iic n).ncard : ℝ) ≤ (419 * √3 / 384 + ε) * √(n : ℝ) := by
  apply of_cert cert49152
  show (((bitset B49152 49152).card : ℝ) + 3) / √((49152 : ℕ) : ℝ) = _
  rw [S49152_card, show ((49152 : ℕ) : ℝ) = (128 : ℝ) ^ 2 * 3 by norm_num,
    div_sqrt _ _ (by norm_num)]
  norm_num

theorem liminf_construction_1894 :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
        ((A ∩ Set.Iic n).ncard : ℝ) ≤ (35 * √3 / 32 + ε) * √(n : ℝ) := by
  apply of_cert cert3072
  show (((bitset B3072 3072).card : ℝ) + 3) / √((3072 : ℕ) : ℝ) = _
  rw [S3072_card, show ((3072 : ℕ) : ℝ) = (32 : ℝ) ^ 2 * 3 by norm_num,
    div_sqrt _ _ (by norm_num)]
  ring

theorem liminf_construction_1912 :
    ∃ A : Set ℕ, (∀ n, 3 ≤ n → ∃ a ∈ A, ∃ b ∈ A, 0 < a ∧ a < b ∧ b < n ∧ a + n = 2 * b) ∧
      ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
        ((A ∩ Set.Iic n).ncard : ℝ) ≤ (53 * √3 / 48 + ε) * √(n : ℝ) := by
  apply of_cert cert768
  show ((S768.card : ℝ) + 3) / √((768 : ℕ) : ℝ) = _
  rw [S768_card, show ((768 : ℕ) : ℝ) = (16 : ℝ) ^ 2 * 3 by norm_num, div_sqrt _ _ (by norm_num)]
  norm_num

end Erdos271.Liminf
