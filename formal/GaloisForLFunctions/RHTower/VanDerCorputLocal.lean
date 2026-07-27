import GaloisForLFunctions.RHTower.VanDerCorput

/-!
# The weighted first-derivative test with local hypotheses

`RHTower.firstDerivTest` asks for `ContDiff ℝ 2 φ` and `ContDiff ℝ 1 A` on all of `ℝ`.  Phases that
arise from a Liouville transform are smooth only on an open ray — the radial prolate phase is
singular at the turning point — so the global form does not apply to them without first
constructing an extension.

This file proves the same estimate from data on the interval alone: derivative functions supplied
as hypotheses, continuity only on `[a,b]`.  The constant and the shape of the bound are unchanged.
-/

open MeasureTheory Set Complex

namespace RHTower

noncomputable section

private theorem intervalIntegrable_of_contOn {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : IntervalIntegrable f volume a b :=
  (uIcc_of_le hab ▸ hf).intervalIntegrable

private theorem intervalIntegrable_of_contOn_real {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) : IntervalIntegrable f volume a b :=
  (uIcc_of_le hab ▸ hf).intervalIntegrable

/-- The amplitude budget from local data: `‖A t‖ ≤ ‖A a‖ + ∫ ‖A'‖` on `[a,b]`. -/
theorem norm_le_budget_of_hasDerivAt {A A' : ℝ → ℂ} {a b : ℝ}
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x) (hA'c : ContinuousOn A' (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖A t‖ ≤ ‖A a‖ + ∫ x in a..b, ‖A' x‖ := by
  have hsubL : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hsubR : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
  have hftc : ∫ x in a..t, A' x = A t - A a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hA x (hsubL (by rwa [uIcc_of_le ht.1] at hx)))
      (intervalIntegrable_of_contOn ht.1 (hA'c.mono hsubL))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x => ‖A' x‖)
    (intervalIntegrable_of_contOn_real ht.1 ((hA'c.norm).mono hsubL))
    (intervalIntegrable_of_contOn_real ht.2 ((hA'c.norm).mono hsubR))
  have hnn' : 0 ≤ ∫ x in t..b, ‖A' x‖ :=
    intervalIntegral.integral_nonneg ht.2 (fun x _ => norm_nonneg _)
  have h3 : ‖∫ x in a..t, A' x‖ ≤ ∫ x in a..t, ‖A' x‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht.1
  calc ‖A t‖ = ‖A a + ∫ x in a..t, A' x‖ := by rw [hftc]; simp
    _ ≤ ‖A a‖ + ‖∫ x in a..t, A' x‖ := norm_add_le _ _
    _ ≤ ‖A a‖ + ∫ x in a..t, ‖A' x‖ := by linarith
    _ ≤ ‖A a‖ + ∫ x in a..b, ‖A' x‖ := by linarith

/-- **First-derivative test, local form.**  With `|φ'| ≥ lam > 0` and `φ'` nondecreasing on `[a,b]`,
the weighted oscillatory integral is at most `4/lam` times the amplitude budget.  All hypotheses are
statements about `[a,b]` only. -/
theorem firstDerivTestOn {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam)
    {φ φ' φ'' : ℝ → ℝ} {A A' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hA'c : ContinuousOn A' (Icc a b))
    (hnn : ∀ x ∈ Icc a b, 0 ≤ φ'' x)
    (hbound : ∀ x ∈ Icc a b, lam ≤ |φ' x|) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖
      ≤ 4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖) / lam := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hφc : ContinuousOn φ (Icc a b) := fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  have hφ'c : ContinuousOn φ' (Icc a b) := fun x hx => (hφ' x hx).continuousAt.continuousWithinAt
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  have hφ'ne : ∀ x ∈ Icc a b, φ' x ≠ 0 := by
    intro x hx hzero
    have := hbound x hx
    rw [hzero, abs_zero] at this
    linarith
  have hIφ'c : ContinuousOn (fun x => Complex.I * (φ' x : ℂ)) (Icc a b) :=
    continuousOn_const.mul ((Complex.continuous_ofReal.comp_continuousOn hφ'c))
  have hIφ'ne : ∀ x ∈ Icc a b, (Complex.I * (φ' x : ℂ)) ≠ 0 := by
    intro x hx
    simp [Complex.I_ne_zero, hφ'ne x hx]
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * φ t) with hEdef
  have hEc : ContinuousOn E (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc))
  have hEnorm : ∀ t : ℝ, ‖E t‖ = 1 := fun t => norm_phase φ t
  set g : ℝ → ℂ := fun t => A t / (Complex.I * (φ' t : ℂ)) with hgdef
  set G : ℝ → ℂ := fun t => (A' t * (Complex.I * (φ' t : ℂ)) -
    A t * (Complex.I * (φ'' t : ℂ))) / (Complex.I * (φ' t : ℂ)) ^ 2 with hGdef
  have hIφ'd : ∀ x ∈ Icc a b,
      HasDerivAt (fun t => Complex.I * (φ' t : ℂ)) (Complex.I * (φ'' x : ℂ)) x :=
    fun x hx => ((hφ' x hx).ofReal_comp).const_mul Complex.I
  have hgd : ∀ x ∈ Icc a b, HasDerivAt g (G x) x := fun x hx =>
    (hA x hx).div (hIφ'd x hx) (hIφ'ne x hx)
  have hEd : ∀ x ∈ Icc a b, HasDerivAt E (E x * (Complex.I * (φ' x : ℂ))) x := fun x hx =>
    (((hφ x hx).ofReal_comp).const_mul Complex.I).cexp
  have hGc : ContinuousOn G (Icc a b) := by
    rw [hGdef]
    refine ContinuousOn.div (ContinuousOn.sub (hA'c.mul hIφ'c)
      (hAc.mul (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ''c))))
      (hIφ'c.pow 2) ?_
    intro x hx
    exact pow_ne_zero 2 (hIφ'ne x hx)
  have hE'c : ContinuousOn (fun t => E t * (Complex.I * (φ' t : ℂ))) (Icc a b) := hEc.mul hIφ'c
  have hgc : ContinuousOn g (Icc a b) := hAc.div hIφ'c hIφ'ne
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => hgd x (by rwa [uIcc_of_le hab] at hx))
    (fun x hx => hEd x (by rwa [uIcc_of_le hab] at hx))
    (intervalIntegrable_of_contOn hab hGc)
    (intervalIntegrable_of_contOn hab hE'c)
  have hpoint : ∀ x ∈ Icc a b, g x * (E x * (Complex.I * (φ' x : ℂ))) = A x * E x := by
    intro x hx
    rw [hgdef]
    have hx0 : ((φ' x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'ne x hx)
    field_simp [hx0, hIφ'ne x hx]
  have hIBP2 : ∫ t in a..b, A t * E t =
      (g b * E b - g a * E a) - ∫ t in a..b, G t * E t := by
    have hIBP' : (∫ t in a..b, G t * E t) +
        (∫ t in a..b, g t * (E t * (Complex.I * (φ' t : ℂ)))) = g b * E b - g a * E a := by
      rw [← hIBP]
      exact (intervalIntegral.integral_add
        (intervalIntegrable_of_contOn hab (hGc.mul hEc))
        (intervalIntegrable_of_contOn hab (hgc.mul hE'c))).symm
    have h2 : ∫ t in a..b, g t * (E t * (Complex.I * (φ' t : ℂ))) = ∫ t in a..b, A t * E t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      exact hpoint t (by rwa [uIcc_of_le hab] at ht)
    rw [h2] at hIBP'
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hIBP')
  have hgb : ‖g b * E b‖ ≤ ‖A b‖ / lam := by
    rw [norm_mul, hEnorm, mul_one, hgdef, norm_div, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound b hbI)
  have hga : ‖g a * E a‖ ≤ ‖A a‖ / lam := by
    rw [norm_mul, hEnorm, mul_one, hgdef, norm_div, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound a haI)
  have hM : ∀ x ∈ Icc a b, ‖A x‖ ≤ ‖A a‖ + ∫ t in a..b, ‖A' t‖ :=
    fun x hx => norm_le_budget_of_hasDerivAt hA hA'c hx
  -- ∫ φ''/φ'² = 1/φ'(a) − 1/φ'(b) ≤ 2/lam
  have hint_phi2 : (∫ t in a..b, φ'' t / (φ' t) ^ 2) ≤ 2 / lam := by
    have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun t => (φ' t)⁻¹) (-(φ'' x) / (φ' x) ^ 2) x := by
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact (hφ' x hx).inv (hφ'ne x hx)
    have hint : IntervalIntegrable (fun t => -(φ'' t) / (φ' t) ^ 2) volume a b :=
      intervalIntegrable_of_contOn_real hab
        (((hφ''c.neg).div (hφ'c.pow 2) (fun x hx => pow_ne_zero 2 (hφ'ne x hx))))
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hcongr : (fun t => -(φ'' t) / (φ' t) ^ 2) = fun t => -(φ'' t / (φ' t) ^ 2) :=
      funext fun t => by ring
    rw [hcongr, intervalIntegral.integral_neg] at h1
    have h2 : (∫ t in a..b, φ'' t / (φ' t) ^ 2) = (φ' a)⁻¹ - (φ' b)⁻¹ := by linarith
    rw [h2]
    have h3 : |(φ' a)⁻¹| ≤ 1 / lam := by
      rw [abs_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hlam (hbound a haI)
    have h4 : |(φ' b)⁻¹| ≤ 1 / lam := by
      rw [abs_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hlam (hbound b hbI)
    have h5 := le_abs_self ((φ' a)⁻¹)
    have h6 := neg_abs_le ((φ' b)⁻¹)
    have : (1 : ℝ) / lam + 1 / lam = 2 / lam := by ring
    linarith
  -- pointwise bound on ‖G‖
  have hGnorm : ∀ x ∈ Icc a b, ‖G x‖ ≤ ‖A' x‖ / lam +
      (‖A a‖ + ∫ t in a..b, ‖A' t‖) * (φ'' x / (φ' x) ^ 2) := by
    intro x hx
    have hden : ‖(Complex.I * (φ' x : ℂ)) ^ 2‖ = (φ' x) ^ 2 := by
      rw [norm_pow, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnum : ‖A' x * (Complex.I * (φ' x : ℂ)) - A x * (Complex.I * (φ'' x : ℂ))‖
        ≤ ‖A' x‖ * |φ' x| + ‖A x‖ * φ'' x := by
      calc ‖A' x * (Complex.I * (φ' x : ℂ)) - A x * (Complex.I * (φ'' x : ℂ))‖
          ≤ ‖A' x * (Complex.I * (φ' x : ℂ))‖ + ‖A x * (Complex.I * (φ'' x : ℂ))‖ :=
            norm_sub_le _ _
        _ = ‖A' x‖ * |φ' x| + ‖A x‖ * |φ'' x| := by
            simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = ‖A' x‖ * |φ' x| + ‖A x‖ * φ'' x := by rw [abs_of_nonneg (hnn x hx)]
    have hb1 : ‖A' x‖ * |φ' x| / (φ' x) ^ 2 = ‖A' x‖ / |φ' x| := by
      rw [← sq_abs]
      field_simp [abs_ne_zero.mpr (hφ'ne x hx)]
    have hb2 : ‖A' x‖ / |φ' x| ≤ ‖A' x‖ / lam :=
      div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound x hx)
    have hφ2nn : 0 ≤ φ'' x / (φ' x) ^ 2 := div_nonneg (hnn x hx) (sq_nonneg _)
    have hb3 : ‖A x‖ * φ'' x / (φ' x) ^ 2
        ≤ (‖A a‖ + ∫ t in a..b, ‖A' t‖) * (φ'' x / (φ' x) ^ 2) := by
      have hshape : ‖A x‖ * φ'' x / (φ' x) ^ 2 = ‖A x‖ * (φ'' x / (φ' x) ^ 2) := by ring
      rw [hshape]
      exact mul_le_mul_of_nonneg_right (hM x hx) hφ2nn
    calc ‖G x‖ = ‖A' x * (Complex.I * (φ' x : ℂ)) - A x * (Complex.I * (φ'' x : ℂ))‖
          / ‖(Complex.I * (φ' x : ℂ)) ^ 2‖ := by rw [hGdef, norm_div]
      _ ≤ (‖A' x‖ * |φ' x| + ‖A x‖ * φ'' x) / (φ' x) ^ 2 := by
          rw [hden]; exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = ‖A' x‖ * |φ' x| / (φ' x) ^ 2 + ‖A x‖ * φ'' x / (φ' x) ^ 2 := by rw [add_div]
      _ ≤ ‖A' x‖ / lam + (‖A a‖ + ∫ t in a..b, ‖A' t‖) * (φ'' x / (φ' x) ^ 2) := by
          linarith [hb1 ▸ hb2, hb3]
  have hIntG : (∫ t in a..b, ‖G t‖) ≤ (∫ t in a..b, ‖A' t‖) / lam +
      (‖A a‖ + ∫ t in a..b, ‖A' t‖) * (2 / lam) := by
    have hii1a : IntervalIntegrable (fun t => ‖A' t‖ / lam) volume a b :=
      intervalIntegrable_of_contOn_real hab ((hA'c.norm).div_const lam)
    have hii1b : IntervalIntegrable (fun t => (‖A a‖ + ∫ t in a..b, ‖A' t‖) *
        (φ'' t / (φ' t) ^ 2)) volume a b :=
      intervalIntegrable_of_contOn_real hab
        ((hφ''c.div (hφ'c.pow 2) (fun x hx => pow_ne_zero 2 (hφ'ne x hx))).const_mul _)
    have hii0 : IntervalIntegrable (fun t => ‖G t‖) volume a b :=
      intervalIntegrable_of_contOn_real hab hGc.norm
    have hmono := intervalIntegral.integral_mono_on hab hii0 (hii1a.add hii1b) hGnorm
    have heq := intervalIntegral.integral_add hii1a hii1b
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at heq
    rw [heq] at hmono
    have hbudnn : 0 ≤ ‖A a‖ + ∫ t in a..b, ‖A' t‖ := by
      have : 0 ≤ ∫ t in a..b, ‖A' t‖ :=
        intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
      linarith [norm_nonneg (A a)]
    have h5 := mul_le_mul_of_nonneg_left hint_phi2 hbudnn
    linarith
  have hfinal : ‖∫ t in a..b, A t * E t‖ ≤ (‖A b‖ + ‖A a‖) / lam + ∫ t in a..b, ‖G t‖ := by
    rw [hIBP2]
    have h1 : ‖(g b * E b - g a * E a) - ∫ t in a..b, G t * E t‖
        ≤ ‖g b * E b - g a * E a‖ + ‖∫ t in a..b, G t * E t‖ := norm_sub_le _ _
    have h2 : ‖g b * E b - g a * E a‖ ≤ ‖g b * E b‖ + ‖g a * E a‖ := norm_sub_le _ _
    have h3 : ‖∫ t in a..b, G t * E t‖ ≤ ∫ t in a..b, ‖G t * E t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have h4 : (∫ t in a..b, ‖G t * E t‖) = ∫ t in a..b, ‖G t‖ := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [norm_mul, hEnorm, mul_one]
    have hdiv : (‖A b‖ + ‖A a‖) / lam = ‖A b‖ / lam + ‖A a‖ / lam := add_div _ _ _
    linarith
  have h6 : 0 ≤ ∫ t in a..b, ‖A' t‖ :=
    intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  have hstep : (‖A b‖ + ‖A a‖) / lam + (∫ t in a..b, ‖G t‖)
      ≤ 4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖) / lam := by
    have hshape : (‖A b‖ + ‖A a‖) / lam + ((∫ t in a..b, ‖A' t‖) / lam +
        (‖A a‖ + ∫ t in a..b, ‖A' t‖) * (2 / lam))
        = (‖A b‖ + 3 * ‖A a‖ + 3 * ∫ t in a..b, ‖A' t‖) / lam := by
      rw [add_div, add_div, add_div, mul_div_assoc]
      ring
    have hle : (‖A b‖ + 3 * ‖A a‖ + 3 * ∫ t in a..b, ‖A' t‖) / lam
        ≤ 4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖) / lam :=
      (div_le_div_iff_of_pos_right hlam).mpr (by
        linarith [h6, norm_nonneg (A a), norm_nonneg (A b)])
    linarith [hIntG, hshape ▸ hle]
  exact hfinal.trans hstep

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory Set Complex

/-- **Second-derivative test, local form.**  With `φ'' ≥ mu > 0` on `[a,b]`, the weighted
oscillatory integral is at most `32/√mu` times the amplitude budget.  As with the first-derivative
test, every hypothesis concerns `[a,b]` only, so the estimate applies to phases that are smooth on an
open ray and singular outside it — a log-chirp `t ↦ c t log t`, for instance, whose second derivative
`c/t` is positive and continuous only on `(0,∞)`. -/
theorem secondDerivTestOn {a b mu : ℝ} (hab : a ≤ b) (hmu : 0 < mu)
    {φ φ' φ'' : ℝ → ℝ} {A A' : ℝ → ℂ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x)
    (hφ' : ∀ x ∈ Icc a b, HasDerivAt φ' (φ'' x) x)
    (hφ''c : ContinuousOn φ'' (Icc a b))
    (hA : ∀ x ∈ Icc a b, HasDerivAt A (A' x) x)
    (hA'c : ContinuousOn A' (Icc a b))
    (hbound : ∀ x ∈ Icc a b, mu ≤ φ'' x) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖
      ≤ 32 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖) / Real.sqrt mu := by
  have hd : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  have hdsq : Real.sqrt mu * Real.sqrt mu = mu := Real.mul_self_sqrt hmu.le
  have hφ'c : ContinuousOn φ' (Icc a b) := fun x hx => (hφ' x hx).continuousAt.continuousWithinAt
  have hAc : ContinuousOn A (Icc a b) := fun x hx => (hA x hx).continuousAt.continuousWithinAt
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * φ t) with hEdef
  have hAEc : ContinuousOn (fun t => A t * E t) (Icc a b) := by
    refine hAc.mul (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_))
    exact Complex.continuous_ofReal.comp_continuousOn
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
  have hA'nn : 0 ≤ ∫ t in a..b, ‖A' t‖ :=
    intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  set M : ℝ := ‖A a‖ + ∫ t in a..b, ‖A' t‖ with hMdef
  have hMnn : 0 ≤ M := by
    have := norm_nonneg (A a)
    linarith
  have hM : ∀ x ∈ Icc a b, ‖A x‖ ≤ M := fun x hx => norm_le_budget_of_hasDerivAt hA hA'c hx
  have hMint : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → (∫ t in p..q, ‖A' t‖) ≤ M := by
    intro p q hap hpq hqb
    have hsub1 : Icc a p ⊆ Icc a b := Icc_subset_Icc le_rfl (hpq.trans hqb)
    have hsub2 : Icc p q ⊆ Icc a b := Icc_subset_Icc hap hqb
    have hsub3 : Icc q b ⊆ Icc a b := Icc_subset_Icc (hap.trans hpq) le_rfl
    have h1 := intervalIntegral.integral_add_adjacent_intervals (f := fun x => ‖A' x‖)
      (intervalIntegrable_of_contOn_real hap ((hA'c.norm).mono hsub1))
      (intervalIntegrable_of_contOn_real hpq ((hA'c.norm).mono hsub2))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (f := fun x => ‖A' x‖)
      (intervalIntegrable_of_contOn_real (hap.trans hpq) ((hA'c.norm).mono
        (Icc_subset_Icc le_rfl hqb)))
      (intervalIntegrable_of_contOn_real hqb ((hA'c.norm).mono hsub3))
    have n1 : 0 ≤ ∫ t in a..p, ‖A' t‖ :=
      intervalIntegral.integral_nonneg hap (fun x _ => norm_nonneg _)
    have n2 : 0 ≤ ∫ t in q..b, ‖A' t‖ :=
      intervalIntegral.integral_nonneg hqb (fun x _ => norm_nonneg _)
    have := norm_nonneg (A a)
    linarith
  have hφ'lo : ∀ {p t : ℝ}, a ≤ p → p ≤ t → t ≤ b → mu * (t - p) ≤ φ' t - φ' p := by
    intro p t hap hpt htb
    have hsub : Icc p t ⊆ Icc a b := Icc_subset_Icc hap htb
    have hftc : ∫ x in p..t, φ'' x = φ' t - φ' p :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hφ' x (hsub (by rwa [uIcc_of_le hpt] at hx)))
        (intervalIntegrable_of_contOn_real hpt (hφ''c.mono hsub))
    have hmono : (∫ _x in p..t, mu) ≤ ∫ x in p..t, φ'' x :=
      intervalIntegral.integral_mono_on hpt intervalIntegral.intervalIntegrable_const
        (intervalIntegrable_of_contOn_real hpt (hφ''c.mono hsub)) (fun x hx => hbound x (hsub hx))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  have hφ'hi : ∀ {q t : ℝ}, a ≤ t → t ≤ q → q ≤ b → mu * (q - t) ≤ φ' q - φ' t := by
    intro q t hat htq hqb
    have hsub : Icc t q ⊆ Icc a b := Icc_subset_Icc hat hqb
    have hftc : ∫ x in t..q, φ'' x = φ' q - φ' t :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x hx => hφ' x (hsub (by rwa [uIcc_of_le htq] at hx)))
        (intervalIntegrable_of_contOn_real htq (hφ''c.mono hsub))
    have hmono : (∫ _x in t..q, mu) ≤ ∫ x in t..q, φ'' x :=
      intervalIntegral.integral_mono_on htq intervalIntegral.intervalIntegrable_const
        (intervalIntegrable_of_contOn_real htq (hφ''c.mono hsub)) (fun x hx => hbound x (hsub hx))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith
  have caseA : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → 0 ≤ φ' p →
      ‖∫ t in p..q, A t * E t‖ ≤ 13 * M / Real.sqrt mu := by
    intro p q hap hpq hqb hp0
    have hpqc : Icc p q ⊆ Icc a b := Icc_subset_Icc hap hqb
    by_cases hshort : q ≤ p + 1 / Real.sqrt mu
    · have h1 : ‖∫ t in p..q, A t * E t‖ ≤ M * (q - p) :=
        norm_integral_le_const_mul_length hpq (fun t ht => hM t (hpqc ht))
      have h2 : M * (q - p) ≤ M * (1 / Real.sqrt mu) := by
        apply mul_le_mul_of_nonneg_left _ hMnn
        linarith
      have h3 : M * (1 / Real.sqrt mu) = M / Real.sqrt mu := by ring
      have h4 : M / Real.sqrt mu ≤ 13 * M / Real.sqrt mu :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      linarith [h3 ▸ h4]
    · have hlong : p + 1 / Real.sqrt mu < q := lt_of_not_ge hshort
      have hinv : 0 < 1 / Real.sqrt mu := one_div_pos.mpr hd
      set u := p + 1 / Real.sqrt mu with hudef
      have hpu : p ≤ u := by rw [hudef]; linarith
      have huq : u ≤ q := hlong.le
      have huc : Icc u q ⊆ Icc a b := Icc_subset_Icc (hap.trans hpu) hqb
      have hsplit : ∫ t in p..q, A t * E t
          = (∫ t in p..u, A t * E t) + ∫ t in u..q, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_contOn hpu (hAEc.mono (Icc_subset_Icc hap (huq.trans hqb))))
          (intervalIntegrable_of_contOn huq (hAEc.mono huc))]
      rw [hsplit]
      have hleft : ‖∫ t in p..u, A t * E t‖ ≤ M * (u - p) :=
        norm_integral_le_const_mul_length hpu
          (fun t ht => hM t (hpqc ⟨ht.1, ht.2.trans huq⟩))
      have hright : ‖∫ t in u..q, A t * E t‖
          ≤ 4 * (‖A q‖ + ‖A u‖ + ∫ t in u..q, ‖A' t‖) / Real.sqrt mu := by
        refine firstDerivTestOn huq hd (fun x hx => hφ x (huc hx)) (fun x hx => hφ' x (huc hx))
          (hφ''c.mono huc) (fun x hx => hA x (huc hx)) (hA'c.mono huc)
          (fun x hx => le_trans hmu.le (hbound x (huc hx))) ?_
        intro t ht
        have h1 : mu * (t - p) ≤ φ' t - φ' p := hφ'lo hap (hpu.trans ht.1) (huc ht).2
        have h2 : mu * (u - p) ≤ mu * (t - p) :=
          mul_le_mul_of_nonneg_left (by linarith [ht.1]) hmu.le
        have h3 : mu * (u - p) = Real.sqrt mu := by
          rw [hudef, show p + 1 / Real.sqrt mu - p = 1 / Real.sqrt mu by ring, mul_one_div,
            div_eq_iff (ne_of_gt hd)]
          exact hdsq.symm
        have h4 : Real.sqrt mu ≤ φ' t := by linarith
        rw [abs_of_nonneg (le_trans hd.le h4)]
        exact h4
      have hAq : ‖A q‖ ≤ M := hM q (hpqc ⟨hpq, le_rfl⟩)
      have hAu : ‖A u‖ ≤ M := hM u (hpqc ⟨hpu, huq⟩)
      have hint : (∫ t in u..q, ‖A' t‖) ≤ M := hMint (hap.trans hpu) huq hqb
      have h7 : M * (u - p) = M / Real.sqrt mu := by rw [hudef]; ring
      have h8 : 4 * (‖A q‖ + ‖A u‖ + ∫ t in u..q, ‖A' t‖) / Real.sqrt mu
          ≤ 12 * M / Real.sqrt mu :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      refine (norm_add_le _ _).trans ?_
      have hsum : M / Real.sqrt mu + 12 * M / Real.sqrt mu = 13 * M / Real.sqrt mu := by
        rw [← add_div]; ring
      linarith
  have caseB : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → φ' q ≤ 0 →
      ‖∫ t in p..q, A t * E t‖ ≤ 13 * M / Real.sqrt mu := by
    intro p q hap hpq hqb hq0
    have hpqc : Icc p q ⊆ Icc a b := Icc_subset_Icc hap hqb
    by_cases hshort : q ≤ p + 1 / Real.sqrt mu
    · have h1 : ‖∫ t in p..q, A t * E t‖ ≤ M * (q - p) :=
        norm_integral_le_const_mul_length hpq (fun t ht => hM t (hpqc ht))
      have h2 : M * (q - p) ≤ M * (1 / Real.sqrt mu) := by
        apply mul_le_mul_of_nonneg_left _ hMnn
        linarith
      have h3 : M * (1 / Real.sqrt mu) = M / Real.sqrt mu := by ring
      have h4 : M / Real.sqrt mu ≤ 13 * M / Real.sqrt mu :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      linarith [h3 ▸ h4]
    · have hlong : p + 1 / Real.sqrt mu < q := lt_of_not_ge hshort
      have hinv : 0 < 1 / Real.sqrt mu := one_div_pos.mpr hd
      set u := q - 1 / Real.sqrt mu with hudef
      have huq : u ≤ q := by rw [hudef]; linarith
      have hpu : p ≤ u := by rw [hudef]; linarith
      have hpc : Icc p u ⊆ Icc a b := Icc_subset_Icc hap (huq.trans hqb)
      have hsplit : ∫ t in p..q, A t * E t
          = (∫ t in p..u, A t * E t) + ∫ t in u..q, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_contOn hpu (hAEc.mono hpc))
          (intervalIntegrable_of_contOn huq (hAEc.mono (Icc_subset_Icc (hap.trans hpu) hqb)))]
      rw [hsplit]
      have hright : ‖∫ t in u..q, A t * E t‖ ≤ M * (q - u) :=
        norm_integral_le_const_mul_length huq
          (fun t ht => hM t (hpqc ⟨hpu.trans ht.1, ht.2⟩))
      have hleft : ‖∫ t in p..u, A t * E t‖
          ≤ 4 * (‖A u‖ + ‖A p‖ + ∫ t in p..u, ‖A' t‖) / Real.sqrt mu := by
        refine firstDerivTestOn hpu hd (fun x hx => hφ x (hpc hx)) (fun x hx => hφ' x (hpc hx))
          (hφ''c.mono hpc) (fun x hx => hA x (hpc hx)) (hA'c.mono hpc)
          (fun x hx => le_trans hmu.le (hbound x (hpc hx))) ?_
        intro t ht
        have h1 : mu * (q - t) ≤ φ' q - φ' t := hφ'hi (hpc ht).1 (ht.2.trans huq) hqb
        have h2 : mu * (q - u) ≤ mu * (q - t) :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) hmu.le
        have h3 : mu * (q - u) = Real.sqrt mu := by
          rw [hudef, show q - (q - 1 / Real.sqrt mu) = 1 / Real.sqrt mu by ring, mul_one_div,
            div_eq_iff (ne_of_gt hd)]
          exact hdsq.symm
        have h4 : φ' t ≤ -Real.sqrt mu := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hAp : ‖A p‖ ≤ M := hM p (hpqc ⟨le_rfl, hpq⟩)
      have hAu : ‖A u‖ ≤ M := hM u (hpqc ⟨hpu, huq⟩)
      have hint : (∫ t in p..u, ‖A' t‖) ≤ M := hMint hap hpu (huq.trans hqb)
      have h7 : M * (q - u) = M / Real.sqrt mu := by rw [hudef]; ring
      have h8 : 4 * (‖A u‖ + ‖A p‖ + ∫ t in p..u, ‖A' t‖) / Real.sqrt mu
          ≤ 12 * M / Real.sqrt mu :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      refine (norm_add_le _ _).trans ?_
      have hsum : M / Real.sqrt mu + 12 * M / Real.sqrt mu = 13 * M / Real.sqrt mu := by
        rw [← add_div]; ring
      linarith
  set B : ℝ := ‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖A' t‖ with hBdef
  have hMB : M ≤ B := by
    have := norm_nonneg (A b)
    linarith
  by_cases h1 : 0 ≤ φ' a
  · refine (caseA le_rfl hab le_rfl h1).trans ?_
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  · have h1 : φ' a < 0 := lt_of_not_ge h1
    by_cases h2 : φ' b ≤ 0
    · refine (caseB le_rfl hab le_rfl h2).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) hd.le
    · have h2 : 0 < φ' b := lt_of_not_ge h2
      obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hφ'c ⟨h1.le, h2.le⟩
      have hsplit : ∫ t in a..b, A t * E t
          = (∫ t in a..c, A t * E t) + ∫ t in c..b, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_contOn hc.1 (hAEc.mono (Icc_subset_Icc le_rfl hc.2)))
          (intervalIntegrable_of_contOn hc.2 (hAEc.mono (Icc_subset_Icc hc.1 le_rfl)))]
      rw [hsplit]
      have hleft := caseB le_rfl hc.1 hc.2 hfc.le
      have hright := caseA hc.1 hc.2 le_rfl hfc.ge
      refine (norm_add_le _ _).trans ?_
      have h26 : 13 * M / Real.sqrt mu + 13 * M / Real.sqrt mu ≤ 32 * B / Real.sqrt mu := by
        rw [← add_div, show 13 * M + 13 * M = 26 * M by ring]
        exact div_le_div_of_nonneg_right (by linarith) hd.le
      linarith

end

end RHTower
