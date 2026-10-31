import Mathlib
open Real Set MeasureTheory

/-! Logarithmic substitution (writeup §5): I(e^T)=∫_0^T h^2 and J(e^T)=Q_T(h),
with h t = A(e^t) e^{-t/2}, K v = e^{-3v/2}/(2-e^{-v})^3.
A is an arbitrary function ℝ → ℝ supported (for the application) on [1,∞);
integrals are over (1, ·) so no integrability hypothesis is needed. -/

noncomputable def hfun (A : ℝ → ℝ) (t : ℝ) : ℝ := A (exp t) * exp (-(t / 2))
noncomputable def Kker (v : ℝ) : ℝ := exp (-(3 * v / 2)) / (2 - exp (-v)) ^ 3

lemma image_exp_Ioo_zero (T : ℝ) : exp '' Ioo 0 T = Ioo 1 (exp T) := by
  rw [image_exp_Ioo, exp_zero]

/-- generic 1D substitution x = e^t on (0,T) -/
lemma subst_exp (g : ℝ → ℝ) (T : ℝ) :
    ∫ x in Ioo 1 (exp T), g x = ∫ t in Ioo 0 T, exp t * g (exp t) := by
  rw [← image_exp_Ioo_zero,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
  simp [abs_of_pos (exp_pos t)]

lemma half_sq (t : ℝ) : exp t = exp (t / 2) ^ 2 := by
  rw [← exp_nat_mul]; ring_nf

theorem I_logsub (A : ℝ → ℝ) (T : ℝ) :
    ∫ x in Ioo 1 (exp T), A x ^ 2 / x ^ 2 = ∫ t in Ioo 0 T, hfun A t ^ 2 := by
  rw [subst_exp]
  refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
  have hp := exp_pos (t / 2)
  simp only [hfun, exp_neg]
  rw [half_sq t]
  field_simp

theorem J_logsub (A : ℝ → ℝ) (T : ℝ) :
    ∫ x in Ioo 1 (exp T), A x * ∫ u in Ioo 1 x, A u / (2 * x - u) ^ 3
      = ∫ τ in Ioo 0 T, hfun A τ * ∫ σ in Ioo 0 τ, Kker (τ - σ) * hfun A σ := by
  rw [subst_exp]
  refine setIntegral_congr_fun measurableSet_Ioo (fun τ _ => ?_)
  rw [subst_exp, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun σ hσ => ?_)
  have hp := exp_pos (τ / 2)
  have hq := exp_pos (σ / 2)
  have hlt : exp (σ / 2) < exp (τ / 2) := exp_lt_exp.mpr (by linarith [hσ.2])
  have e1 : exp (-(3 * (τ - σ) / 2)) = exp (σ / 2) ^ 3 / exp (τ / 2) ^ 3 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_sub]; ring_nf
  have e2 : exp (-(τ - σ)) = exp (σ / 2) ^ 2 / exp (τ / 2) ^ 2 := by
    rw [← exp_nat_mul, ← exp_nat_mul, ← exp_sub]; ring_nf
  have e3 : exp (-(τ / 2)) = 1 / exp (τ / 2) := by rw [exp_neg]; ring
  have e4 : exp (-(σ / 2)) = 1 / exp (σ / 2) := by rw [exp_neg]; ring
  simp only [hfun, Kker]
  rw [e1, e2, e3, e4, half_sq τ, half_sq σ]
  set p := exp (τ / 2)
  set q := exp (σ / 2)
  have hd : 2 * p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  have hd' : 2 - q ^ 2 / p ^ 2 ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : q ^ 2 = 2 * p ^ 2 := by field_simp at h; linarith
    exact hd (by linarith)
  field_simp


/-! Counting function of a finite set P ⊂ ℝ and integrability of the I-integrand. -/
noncomputable def Acount (P : Finset ℝ) (t : ℝ) : ℝ :=
  ∑ p ∈ P, (Ici p).indicator (fun _ => (1:ℝ)) t

lemma Acount_measurable (P : Finset ℝ) : Measurable (Acount P) := by
  unfold Acount
  exact Finset.measurable_sum _ (fun p _ => measurable_const.indicator measurableSet_Ici)

lemma Acount_nonneg (P : Finset ℝ) (t : ℝ) : 0 ≤ Acount P t :=
  Finset.sum_nonneg (fun _p _ => indicator_nonneg (fun _ _ => zero_le_one) t)

lemma Acount_le (P : Finset ℝ) (t : ℝ) : Acount P t ≤ P.card := by
  unfold Acount
  calc ∑ p ∈ P, (Ici p).indicator (fun _ => (1:ℝ)) t ≤ ∑ _p ∈ P, (1:ℝ) :=
        Finset.sum_le_sum (fun _p _ => indicator_le_self' (fun _ _ => zero_le_one) t |>.trans (le_refl _))
    _ = P.card := by simp

theorem I_integrable (P : Finset ℝ) (X : ℝ) :
    IntegrableOn (fun x => Acount P x ^ 2 / x ^ 2) (Ioo 1 X) := by
  refine Measure.integrableOn_of_bounded (M := (P.card : ℝ) ^ 2) measure_Ioo_lt_top.ne ?_ ?_
  · exact (((Acount_measurable P).pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall (fun x hx => ?_))
    have hx1 : (1:ℝ) < x := hx.1
    have h0 := Acount_nonneg P x
    have h1 := Acount_le P x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have : Acount P x ^ 2 ≤ (P.card : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have : (1:ℝ) ≤ x ^ 2 := one_le_pow₀ hx1.le
    nlinarith [sq_nonneg (P.card : ℝ)]

/-- integrability transfers through the substitution (so the h²-integral is a genuine
Lebesgue integral of an integrable function, not a junk value). -/
theorem h_sq_integrable (P : Finset ℝ) (T : ℝ) :
    IntegrableOn (fun t => hfun (Acount P) t ^ 2) (Ioo 0 T) := by
  have := (integrableOn_image_iff_integrableOn_abs_deriv_smul (f := exp) (f' := exp) (s := Ioo 0 T) measurableSet_Ioo
      (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt) exp_injective.injOn
      (fun x => Acount P x ^ 2 / x ^ 2)).mp (by rw [image_exp_Ioo_zero]; exact I_integrable P _)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioo
  have hp := exp_pos (t / 2)
  simp only [hfun, exp_neg, smul_eq_mul, abs_of_pos (exp_pos t)]
  rw [half_sq t]
  field_simp

#print axioms I_integrable
#print axioms h_sq_integrable

#print axioms I_logsub
#print axioms J_logsub
