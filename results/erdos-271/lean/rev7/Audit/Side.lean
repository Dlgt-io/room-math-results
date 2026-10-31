import Audit.Bridge
import Audit.Moy
import Audit.Alpha

/-!
# Side items of the (6.1)/limit step

* `AS S x`: the counting function `#(S ∩ (0, x])` of `S ⊆ ℕ` at real `x`; `Pfin S X = S ∩ [0, X]`.
* `Acount_Pfin`: the real counting function of `Pr (Pfin S X)` equals `AS S` on `[0, X]`.
* `I0_indep`, `members_indep`: the initial terms `I(x0)` and `∑_{s<a≤x0, a∈P} 1/a` do not
  depend on `X ≥ x0`.
* `D_nonneg`, `E_le`: `D ≥ 0` and `E ≤ U²/2`.
* `lower_env`: Lemma 1 gives eventually `(7/5)√x ≤ AS S x`.
* `env_of_limsup`: `limsup AS/√x < U` (bounded case) gives eventually `AS S x ≤ U√x`.
* `beta_eq` (`3/2 - 4β = α`), `kappa_pos`, `alpha_lt_one`, `Cstar_gt_one`.
-/

open MeasureTheory Set Real Finset Filter
open Erdos271.FiniteIntegrals

namespace Erdos271.Side

variable (S : Set ℕ) [DecidablePred (· ∈ S)]

/-- `S ∩ [0, X]`. -/
def Pfin (X : ℕ) : Finset ℕ := (range (X + 1)).filter (· ∈ S)

/-- Counting function `#(S ∩ (0, x])` at real `x`. -/
noncomputable def AS (x : ℝ) : ℝ :=
  (((range (⌊x⌋₊ + 1)).filter (fun n => n ∈ S ∧ 0 < n)).card : ℝ)

theorem AS_nonneg (x : ℝ) : 0 ≤ AS S x := Nat.cast_nonneg _

theorem AS_floor (x : ℝ) : AS S x = AS S (⌊x⌋₊ : ℝ) := by
  unfold AS; rw [Nat.floor_natCast]

theorem Acount_Pfin {X : ℕ} {x : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) :
    Acount (Erdos271.Glue.Pr (Pfin S X)) x = AS S x := by
  unfold Acount Erdos271.Glue.Pr AS
  rw [Finset.sum_image (Erdos271.Glue.cast_injOn _)]
  simp only [Set.indicator, Set.mem_Ici]
  rw [Finset.sum_boole]
  congr 2
  have hfl : ⌊x⌋₊ ≤ X := Nat.floor_le_of_le hxX
  have key : ∀ n : ℕ, (n : ℝ) ≤ x ↔ n ≤ ⌊x⌋₊ := fun n => (Nat.le_floor_iff hx).symm
  ext n
  simp only [Pfin, Finset.mem_filter, Finset.mem_range, key]
  constructor
  · rintro ⟨⟨⟨_, h1⟩, h2⟩, h3⟩; exact ⟨by omega, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩

/-- The `Acnt` of `Pfin S X` at `t ≤ X` is `AS S t`. -/
theorem Acnt_Pfin {X t : ℕ} (htX : t ≤ X) :
    (Erdos271.MemberTail.Acnt (Pfin S X) t : ℝ) = AS S t := by
  rw [← Erdos271.Glue.Acount_Pr, Acount_Pfin S (Nat.cast_nonneg _) (by exact_mod_cast htX)]

theorem Pfin_card {X : ℕ} :
    (((Erdos271.Glue.Pr (Pfin S X)).card : ℕ) : ℝ) = AS S X := by
  rw [Erdos271.Glue.card_Pr (X := X)]
  · exact Acnt_Pfin S le_rfl
  · intro p hp; have := (Finset.mem_filter.mp hp).1; rw [Finset.mem_range] at this; omega

theorem I0_indep {x0 : ℝ} {X : ℕ} (hX : x0 ≤ X) :
    ∫ x in Ioo 1 x0, Acount (Erdos271.Glue.Pr (Pfin S X)) x ^ 2 / x ^ 2
      = ∫ x in Ioo 1 x0, AS S x ^ 2 / x ^ 2 := by
  refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
  rw [Acount_Pfin S (by linarith [hx.1]) (by linarith [hx.2])]

theorem members_indep {s x0 X : ℕ} (hX : x0 ≤ X) :
    ∑ z ∈ (Finset.Ioc s x0).filter (fun z => z ∈ Pfin S X), ((z : ℝ))⁻¹
      = ∑ z ∈ (Finset.Ioc s x0).filter (fun z => z ∈ S), ((z : ℝ))⁻¹ := by
  congr 1
  apply Finset.filter_congr
  intro z hz
  rw [Finset.mem_Ioc] at hz
  simp only [Pfin, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by omega, h⟩

theorem D_nonneg {h : ℝ → ℝ} {a b U : ℝ} (hab : a ≤ b) (hb : ∀ t ∈ Icc a b, h t ≤ U) :
    0 ≤ ∫ t in a..b, (U - h t) :=
  intervalIntegral.integral_nonneg hab (fun t ht => sub_nonneg.mpr (hb t ht))

theorem E_le (P : Finset ℝ) {X U : ℝ} (hX : 0 < X)
    (hcard : (P.card : ℝ) ≤ U * √X) (hE : boundaryTerm P X ≤ (P.card : ℝ) ^ 2 / (2 * X)) :
    boundaryTerm P X ≤ U ^ 2 / 2 := by
  have h2 : (P.card : ℝ) ^ 2 ≤ U ^ 2 * X := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    rwa [mul_pow, Real.sq_sqrt hX.le] at this
  calc boundaryTerm P X ≤ (P.card : ℝ) ^ 2 / (2 * X) := hE
    _ ≤ U ^ 2 * X / (2 * X) := div_le_div_of_nonneg_right h2 (by positivity)
    _ = U ^ 2 / 2 := by field_simp

/-- **Lemma 1, eventual form**: `(7/5)√x ≤ AS S x` for `x ≥ (156 + 50 s)²`. -/
theorem lower_env (s : ℕ)
    (hcov : ∀ z, s < z → z ∉ S → ∃ a ∈ S, ∃ b ∈ S, a < b ∧ 2 * b - a = z) :
    ∀ x : ℝ, (156 + 50 * (s : ℝ)) ^ 2 ≤ x → (7 / 5) * √x ≤ AS S x := by
  intro x hx
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  set X := ⌊x⌋₊ with hXdef
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hXx : x < X + 1 := Nat.lt_floor_add_one x
  have hm := Erdos271.Moy.moy_set S s hcov X
  set A := (((range (X + 1)).filter (· ∈ S)).filter (fun p => 0 < p ∧ p ≤ X)).card with hA
  have hAS : AS S x = (A : ℝ) := by
    unfold AS; rw [← hXdef, hA]
    congr 2
    ext n; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3, _⟩; exact ⟨h1, h2, h3⟩
  rw [hAS]
  have hmr : (2 * X : ℝ) ≤ (A : ℝ) ^ 2 + 3 * A + 2 * s := by exact_mod_cast hm
  set u := √x with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hux : u ^ 2 = x := Real.sq_sqrt hx0
  have hu1 : 156 + 50 * (s : ℝ) ≤ u := by
    rw [hu]; exact Real.le_sqrt_of_sq_le hx
  by_contra hlt
  push Not at hlt
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hA2 : (A : ℝ) ^ 2 ≤ (7 / 5 * u) ^ 2 := pow_le_pow_left₀ hA0 hlt.le 2
  nlinarith

theorem env_of_limsup {U : ℝ}
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun x => AS S x / √x))
    (h : limsup (fun x => AS S x / √x) atTop < U) :
    ∀ᶠ x in atTop, AS S x ≤ U * √x := by
  filter_upwards [eventually_lt_of_limsup_lt h hb, eventually_gt_atTop 0] with x hx hx0
  have := Real.sqrt_pos.mpr hx0
  rw [div_lt_iff₀ this] at hx
  exact hx.le

open Erdos271.Alpha in
theorem beta_eq : (3 : ℝ) / 2 - 4 * (3 / 8 - Real.log (1 + √2) / (8 * √2)) = α := by
  unfold α
  have : (0 : ℝ) < √2 := by positivity
  field_simp; ring

open Erdos271.Alpha in
theorem kappa_pos {U : ℝ} (hU : 0 ≤ U) (hU2 : U < 9 / 5) :
    0 < 2 * α * U - (3 / 2) * (U - 7 / 5) := by
  have := alpha_gt_three_tenths
  have hp : 0 ≤ (α - 3 / 10) * U := mul_nonneg (by linarith) hU
  nlinarith

open Erdos271.Alpha in
theorem alpha_lt_one : α < 1 := by
  unfold α
  have hs : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hl : Real.log (1 + √2) ≤ √2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + √2); linarith
  rw [div_lt_one (by positivity)]
  linarith

open Erdos271.Alpha in
theorem Cstar_gt_one : 1 < 1 / √α := by
  have h0 := alpha_pos
  have h1 := alpha_lt_one
  have hs : √α < 1 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt h0.le h1
  rw [lt_div_iff₀ (Real.sqrt_pos.mpr h0)]; linarith

end Erdos271.Side
