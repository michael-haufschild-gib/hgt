import Mathlib

open MeasureTheory intervalIntegral Complex Set

noncomputable section

namespace RHTower

/-- Chain-rule derivative of `t ↦ Complex.exp (Complex.I * φ t)`. -/
theorem hasDerivAt_phase {φ : ℝ → ℝ} (t : ℝ) (h : HasDerivAt φ (deriv φ t) t) :
    HasDerivAt (fun t => Complex.exp (Complex.I * φ t))
      (Complex.exp (Complex.I * φ t) * (Complex.I * ↑(deriv φ t))) t := by
  have h1 : HasDerivAt (fun t => (↑(φ t) : ℂ)) (↑(deriv φ t)) t := h.ofReal_comp
  have h2 : HasDerivAt (fun t => Complex.I * (↑(φ t) : ℂ))
      (Complex.I * (↑(deriv φ t))) t := h1.const_mul Complex.I
  exact h2.cexp

/-- Norm of the phase exponential is one. -/
theorem norm_phase (φ : ℝ → ℝ) (t : ℝ) :
    ‖Complex.exp (Complex.I * φ t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

private theorem intervalIntegrable_of_continuousOn_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) : IntervalIntegrable f volume a b :=
  (uIcc_of_le hab ▸ hf).intervalIntegrable

private theorem intervalIntegrable_of_continuousOn_Icc_real {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) : IntervalIntegrable f volume a b :=
  (uIcc_of_le hab ▸ hf).intervalIntegrable

/-- Amplitude budget: `‖A t‖ ≤ ‖A a‖ + ∫ ‖A'‖` on `[a,b]`. -/
theorem norm_le_deriv_budget {A : ℝ → ℂ} {a b : ℝ} (hA : ContDiff ℝ 1 A)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ‖A t‖ ≤ ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ := by
  have hA1 : Continuous (deriv A) := hA.continuous_deriv (le_refl 1)
  have hAd : ∀ t, HasDerivAt A (deriv A t) t :=
    fun t => (hA.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hftc : ∫ x in a..t, deriv A x = A t - A a :=
    intervalIntegral.integral_deriv_eq_sub (fun x _ => (hAd x).differentiableAt)
      (intervalIntegrable_of_continuousOn_Icc ht.1
        ((hA1.continuousOn).mono (Set.Icc_subset_Icc (le_refl a) ht.2)))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun x => ‖deriv A x‖)
    (intervalIntegrable_of_continuousOn_Icc_real ht.1
      ((hA1.norm.continuousOn).mono (Set.Icc_subset_Icc (le_refl a) ht.2)))
    (intervalIntegrable_of_continuousOn_Icc_real ht.2
      ((hA1.norm.continuousOn).mono (Set.Icc_subset_Icc ht.1 (le_refl b))))
  have hnn' : 0 ≤ ∫ x in t..b, ‖deriv A x‖ :=
    intervalIntegral.integral_nonneg ht.2 (fun x _ => norm_nonneg _)
  have h3 : ‖∫ x in a..t, deriv A x‖ ≤ ∫ x in a..t, ‖deriv A x‖ :=
    intervalIntegral.norm_integral_le_integral_norm ht.1
  have h4 : (∫ x in a..t, ‖deriv A x‖) ≤ ∫ x in a..b, ‖deriv A x‖ := by linarith [hsplit]
  calc ‖A t‖ = ‖A a + ∫ x in a..t, deriv A x‖ := by rw [hftc]; simp [add_sub_cancel]
    _ ≤ ‖A a‖ + ‖∫ x in a..t, deriv A x‖ := norm_add_le _ _
    _ ≤ ‖A a‖ + ∫ x in a..t, ‖deriv A x‖ := by linarith [h3]
    _ ≤ ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ := by linarith [h4]

/-- Trivial bound on a short interval. -/
theorem norm_integral_le_const_mul_length {φ : ℝ → ℝ} {A : ℝ → ℂ} {a b C : ℝ} (hab : a ≤ b)
    (hC : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ C) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖ ≤ C * (b - a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t =>
    A t * Complex.exp (Complex.I * φ t)) (a := a) (b := b) (C := C) (fun x hx => by
      rw [uIoc_of_le hab] at hx
      rw [norm_mul, norm_phase, mul_one]
      exact hC x (Set.Ioc_subset_Icc_self hx))
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- First derivative test, covering both signs of `φ'`. If `|φ'| ≥ λ > 0` and
`φ'' ≥ 0` on `[a,b]`, then `∫ A e^{iφ}` is at most `4/λ` times the amplitude
budget `‖A b‖ + ‖A a‖ + ∫ ‖A'‖`. -/
theorem firstDerivTest {φ : ℝ → ℝ} {A : ℝ → ℂ} {a b lam : ℝ}
    (hab : a ≤ b) (hlam : 0 < lam)
    (hφ : ContDiff ℝ 2 φ)
    (hnn : ∀ t ∈ Set.Icc a b, 0 ≤ deriv (deriv φ) t)
    (hbound : ∀ t ∈ Set.Icc a b, lam ≤ |deriv φ t|)
    (hA : ContDiff ℝ 1 A) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖ ≤
      4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖deriv A t‖) / lam := by
  have hφ1 : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
  have hφ2 : Continuous (deriv (deriv φ)) :=
    (ContDiff.deriv' hφ).continuous_deriv (le_refl 1)
  have hA1 : Continuous (deriv A) := hA.continuous_deriv (le_refl 1)
  have hAc : Continuous A := hA.continuous
  have hφd : ∀ t, HasDerivAt φ (deriv φ t) t :=
    fun t => (hφ.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hφ2d : ∀ t, HasDerivAt (deriv φ) (deriv (deriv φ) t) t :=
    fun t => (hφ.differentiable_deriv_two).differentiableAt.hasDerivAt
  have hAd : ∀ t, HasDerivAt A (deriv A t) t :=
    fun t => (hA.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hφ'ne : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0 := by
    intro t ht hzero
    have hb := hbound t ht
    rw [hzero, abs_zero] at hb
    linarith
  have hIφ'c : ContinuousOn (fun t => Complex.I * ↑(deriv φ t)) (Set.Icc a b) :=
    continuousOn_const.mul ((continuous_ofReal.comp hφ1).continuousOn)
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * φ t) with hEdef
  have hEc : Continuous E := by
    apply Complex.continuous_exp.comp
    exact continuous_const.mul (continuous_ofReal.comp hφ.continuous)
  set g : ℝ → ℂ := fun t => A t / (Complex.I * ↑(deriv φ t)) with hgdef
  set g' : ℝ → ℂ := fun t => (deriv A t * (Complex.I * ↑(deriv φ t)) -
    A t * (Complex.I * ↑(deriv (deriv φ) t))) / (Complex.I * ↑(deriv φ t))^2
  have hIφ'd : ∀ t ∈ Set.Icc a b, HasDerivAt (fun t => Complex.I * ↑(deriv φ t))
      (Complex.I * ↑(deriv (deriv φ) t)) t := fun t ht =>
    ((hφ2d t).ofReal_comp).const_mul Complex.I
  have hIφ'ne : ∀ t ∈ Set.Icc a b, (Complex.I * ↑(deriv φ t)) ≠ 0 := by
    intro t ht
    simp [Complex.I_ne_zero, hφ'ne t ht]
  have hg'd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t := fun t ht =>
    (hAd t).div (hIφ'd t ht) (hIφ'ne t ht)
  have hE'd : ∀ t ∈ Set.Icc a b, HasDerivAt E
      (E t * (Complex.I * ↑(deriv φ t))) t := fun t _ => hasDerivAt_phase t (hφd t)
  have hg'c : ContinuousOn g' (Set.Icc a b) := by
    apply ContinuousOn.div
    · apply ContinuousOn.sub
      · exact (hA1.continuousOn).mul hIφ'c
      · exact (hAc.continuousOn).mul
          (continuousOn_const.mul ((continuous_ofReal.comp hφ2).continuousOn))
    · exact hIφ'c.pow 2
    · intro t ht
      simp [pow_eq_zero_iff, Complex.I_ne_zero, hφ'ne t ht]
  have hE'c : ContinuousOn (fun t => E t * (Complex.I * ↑(deriv φ t))) (Set.Icc a b) :=
    (hEc.continuousOn).mul hIφ'c
  have hgc : ContinuousOn g (Set.Icc a b) := (hAc.continuousOn).div hIφ'c hIφ'ne
  -- IBP: ∫(g'·E + g·E') = g·E|_a^b
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x hx => hg'd x (show x ∈ Set.Icc a b from by rwa [uIcc_of_le hab] at hx))
    (fun x hx => hE'd x (show x ∈ Set.Icc a b from by rwa [uIcc_of_le hab] at hx))
    (intervalIntegrable_of_continuousOn_Icc hab hg'c)
    (intervalIntegrable_of_continuousOn_Icc hab hE'c)
  have hpoint : ∀ t ∈ Set.Icc a b, g t * (E t * (Complex.I * ↑(deriv φ t))) =
      A t * E t := by
    intro t ht
    rw [hgdef]
    have hx : (↑(deriv φ t) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hφ'ne t ht)
    field_simp [hx, hIφ'ne t ht]
  have hIBP2 : ∫ t in a..b, A t * E t =
      (g b * E b - g a * E a) - ∫ t in a..b, g' t * E t := by
    have hIBP' : (∫ t in a..b, g' t * E t) +
        (∫ t in a..b, g t * (E t * (Complex.I * ↑(deriv φ t)))) = g b * E b - g a * E a := by
      rw [← hIBP]
      exact (intervalIntegral.integral_add
        (intervalIntegrable_of_continuousOn_Icc hab (hg'c.mul hEc.continuousOn))
        (intervalIntegrable_of_continuousOn_Icc hab (hgc.mul hE'c))).symm
    have h2 : ∫ t in a..b, g t * (E t * (Complex.I * ↑(deriv φ t))) =
        ∫ t in a..b, A t * E t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t (by rwa [uIcc_of_le hab] at ht)
    rw [h2] at hIBP'
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hIBP')
  -- norm bounds
  have hgb : ‖g b * E b‖ ≤ ‖A b‖ / lam := by
    rw [norm_mul, norm_phase, mul_one, hgdef, norm_div, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound b ⟨hab, le_refl b⟩)
  have hga : ‖g a * E a‖ ≤ ‖A a‖ / lam := by
    rw [norm_mul, norm_phase, mul_one, hgdef, norm_div, norm_mul, norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound a ⟨le_refl a, hab⟩)
  have hM : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ := by
    intro t ht
    have hftc : ∫ x in a..t, deriv A x = A t - A a :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => (hAd x).differentiableAt)
        (intervalIntegrable_of_continuousOn_Icc ht.1
          ((hA1.continuousOn).mono (Set.Icc_subset_Icc (le_refl a) ht.2)))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (f := fun x => ‖deriv A x‖)
      (intervalIntegrable_of_continuousOn_Icc_real ht.1
        ((hA1.norm.continuousOn).mono (Set.Icc_subset_Icc (le_refl a) ht.2)))
      (intervalIntegrable_of_continuousOn_Icc_real ht.2
        ((hA1.norm.continuousOn).mono (Set.Icc_subset_Icc ht.1 (le_refl b))))
    have hnn' : 0 ≤ ∫ x in t..b, ‖deriv A x‖ :=
      intervalIntegral.integral_nonneg ht.2 (fun x _ => norm_nonneg _)
    have h3 : ‖∫ x in a..t, deriv A x‖ ≤ ∫ x in a..t, ‖deriv A x‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h4 : (∫ x in a..t, ‖deriv A x‖) ≤ ∫ x in a..b, ‖deriv A x‖ := by linarith [hsplit]
    calc ‖A t‖ = ‖A a + ∫ x in a..t, deriv A x‖ := by rw [hftc]; simp [add_sub_cancel]
      _ ≤ ‖A a‖ + ‖∫ x in a..t, deriv A x‖ := norm_add_le _ _
      _ ≤ ‖A a‖ + ∫ x in a..t, ‖deriv A x‖ := by linarith [h3]
      _ ≤ ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ := by linarith [h4]
  -- ∫ φ''/φ'² = 1/φ'(a) − 1/φ'(b) ≤ 2/λ
  have hint_phi2 : (∫ t in a..b, (deriv (deriv φ) t) / (deriv φ t)^2) ≤ 2 / lam := by
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => (deriv φ t)⁻¹) (f' := fun t => -(deriv (deriv φ) t) / (deriv φ t)^2)
      (fun x hx => (hφ2d x).inv (hφ'ne x (show x ∈ Set.Icc a b from by rwa [uIcc_of_le hab] at hx)))
      ((intervalIntegrable_of_continuousOn_Icc_real hab (((hφ2.continuousOn).neg).div
        (hφ1.continuousOn.pow 2) (fun t ht => pow_ne_zero 2 (hφ'ne t ht)))))
    have hcongr : (fun t => -(deriv (deriv φ) t) / (deriv φ t)^2) =
        fun t => -((deriv (deriv φ) t) / (deriv φ t)^2) := funext fun t => by ring
    rw [hcongr, intervalIntegral.integral_neg] at h1
    have h2 : (∫ t in a..b, (deriv (deriv φ) t) / (deriv φ t)^2) =
        (deriv φ a)⁻¹ - (deriv φ b)⁻¹ := by linarith [h1]
    rw [h2]
    have h3 : |(deriv φ a)⁻¹| ≤ 1 / lam := by
      rw [abs_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hlam (hbound a ⟨le_refl a, hab⟩)
    have h4 : |(deriv φ b)⁻¹| ≤ 1 / lam := by
      rw [abs_inv, inv_eq_one_div]
      exact one_div_le_one_div_of_le hlam (hbound b ⟨hab, le_refl b⟩)
    calc (deriv φ a)⁻¹ - (deriv φ b)⁻¹ ≤ |(deriv φ a)⁻¹| + |(deriv φ b)⁻¹| := by
          have hle1 := le_abs_self ((deriv φ a)⁻¹)
          have hle2 := neg_abs_le ((deriv φ b)⁻¹)
          linarith
      _ ≤ 1 / lam + 1 / lam := by linarith [h3, h4]
      _ = 2 / lam := by ring
  -- ∫ ‖g'‖
  have hg'_norm : ∀ t ∈ Set.Icc a b, ‖g' t‖ ≤ ‖deriv A t‖ / lam +
      (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * ((deriv (deriv φ) t) / (deriv φ t)^2) := by
    intro t ht
    have hden : ‖(Complex.I * ↑(deriv φ t))^2‖ = (deriv φ t)^2 := by
      rw [norm_pow, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnum : ‖deriv A t * (Complex.I * ↑(deriv φ t)) -
        A t * (Complex.I * ↑(deriv (deriv φ) t))‖ ≤
        ‖deriv A t‖ * |deriv φ t| + ‖A t‖ * (deriv (deriv φ) t) := by
      calc ‖deriv A t * (Complex.I * ↑(deriv φ t)) -
          A t * (Complex.I * ↑(deriv (deriv φ) t))‖
          ≤ ‖deriv A t * (Complex.I * ↑(deriv φ t))‖ +
            ‖A t * (Complex.I * ↑(deriv (deriv φ) t))‖ := norm_sub_le _ _
        _ = ‖deriv A t‖ * |deriv φ t| + ‖A t‖ * |deriv (deriv φ) t| := by
            simp only [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = ‖deriv A t‖ * |deriv φ t| + ‖A t‖ * (deriv (deriv φ) t) := by
            simp only [abs_of_nonneg (hnn t ht)]
    have hb1 : ‖deriv A t‖ * |deriv φ t| / (deriv φ t)^2 = ‖deriv A t‖ / |deriv φ t| := by
      rw [← sq_abs]
      field_simp [abs_ne_zero.mpr (hφ'ne t ht)]
    have hb2 : ‖deriv A t‖ / |deriv φ t| ≤ ‖deriv A t‖ / lam :=
      div_le_div_of_nonneg_left (norm_nonneg _) hlam (hbound t ht)
    have hb3 : ‖A t‖ * (deriv (deriv φ) t) / (deriv φ t)^2 ≤
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * ((deriv (deriv φ) t) / (deriv φ t)^2) := by
      have hφ2nn : 0 ≤ (deriv (deriv φ) t) / (deriv φ t)^2 :=
        div_nonneg (hnn t ht) (sq_nonneg _)
      have hshape : ‖A t‖ * (deriv (deriv φ) t) / (deriv φ t)^2 =
          ‖A t‖ * ((deriv (deriv φ) t) / (deriv φ t)^2) := by ring
      rw [hshape]
      exact mul_le_mul_of_nonneg_right (hM t ht) hφ2nn
    calc ‖g' t‖ = ‖deriv A t * (Complex.I * ↑(deriv φ t)) -
          A t * (Complex.I * ↑(deriv (deriv φ) t))‖ / ‖(Complex.I * ↑(deriv φ t))^2‖ := by
          rw [norm_div]
      _ ≤ (‖deriv A t‖ * |deriv φ t| + ‖A t‖ * (deriv (deriv φ) t)) / (deriv φ t)^2 := by
          rw [hden]
          exact div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = ‖deriv A t‖ * |deriv φ t| / (deriv φ t)^2 +
          ‖A t‖ * (deriv (deriv φ) t) / (deriv φ t)^2 := by
          rw [add_div]
      _ ≤ ‖deriv A t‖ / lam +
          (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * ((deriv (deriv φ) t) / (deriv φ t)^2) := by
          linarith [hb1 ▸ hb2, hb3]
  have hInt_g' : (∫ t in a..b, ‖g' t‖) ≤
      (∫ t in a..b, ‖deriv A t‖) / lam +
      (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * (2 / lam) := by
    have hii1 : IntervalIntegrable (fun t => ‖deriv A t‖ / lam +
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * ((deriv (deriv φ) t) / (deriv φ t)^2))
        volume a b := by
      apply intervalIntegrable_of_continuousOn_Icc_real hab
      apply ContinuousOn.add
      · exact (hA1.norm.continuousOn).div_const lam
      · exact (((hφ2.continuousOn).div (hφ1.continuousOn.pow 2) (fun t ht =>
          pow_ne_zero 2 (hφ'ne t ht)))).const_mul (‖A a‖ + ∫ x in a..b, ‖deriv A x‖)
    have hii0 : IntervalIntegrable (fun t => ‖g' t‖) volume a b :=
      intervalIntegrable_of_continuousOn_Icc_real hab (hg'c.norm)
    have hmono := intervalIntegral.integral_mono_on hab hii0 hii1 hg'_norm
    have heq : (∫ t in a..b, (‖deriv A t‖ / lam +
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * ((deriv (deriv φ) t) / (deriv φ t)^2))) =
        (∫ t in a..b, ‖deriv A t‖) / lam +
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) *
          (∫ t in a..b, (deriv (deriv φ) t) / (deriv φ t)^2) := by
      have hii1a : IntervalIntegrable (fun t => ‖deriv A t‖ / lam) volume a b :=
        intervalIntegrable_of_continuousOn_Icc_real hab ((hA1.norm.continuousOn).div_const lam)
      have hii1b : IntervalIntegrable (fun t => (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) *
          ((deriv (deriv φ) t) / (deriv φ t)^2)) volume a b :=
        intervalIntegrable_of_continuousOn_Icc_real hab
          (((hφ2.continuousOn).div (hφ1.continuousOn.pow 2) (fun t ht =>
            pow_ne_zero 2 (hφ'ne t ht))).const_mul (‖A a‖ + ∫ x in a..b, ‖deriv A x‖))
      have heq1 := intervalIntegral.integral_add hii1a hii1b
      rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at heq1
      exact heq1
    rw [heq] at hmono
    have h5 : (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) *
          (∫ t in a..b, (deriv (deriv φ) t) / (deriv φ t)^2) ≤
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * (2 / lam) := by
      apply mul_le_mul_of_nonneg_left hint_phi2
      have h6 : 0 ≤ ∫ x in a..b, ‖deriv A x‖ :=
        intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
      linarith [norm_nonneg (A a), h6]
    linarith [hmono, h5]
  -- assemble
  have hfinal : ‖∫ t in a..b, A t * E t‖ ≤
      (‖A b‖ + ‖A a‖) / lam + (∫ t in a..b, ‖g' t‖) := by
    rw [hIBP2]
    have h1 : ‖(g b * E b - g a * E a) - ∫ t in a..b, g' t * E t‖ ≤
        ‖g b * E b - g a * E a‖ + ‖∫ t in a..b, g' t * E t‖ := norm_sub_le _ _
    have h2 : ‖g b * E b - g a * E a‖ ≤ ‖g b * E b‖ + ‖g a * E a‖ := norm_sub_le _ _
    have h3 : ‖∫ t in a..b, g' t * E t‖ ≤ ∫ t in a..b, ‖g' t * E t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    have h4 : (∫ t in a..b, ‖g' t * E t‖) = ∫ t in a..b, ‖g' t‖ := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hEdef]
      rw [norm_mul, norm_phase, mul_one]
    have h5 : (∫ t in a..b, ‖g' t * E t‖) ≤ ∫ t in a..b, ‖g' t‖ := by
      apply intervalIntegral.integral_mono_on hab
      · exact intervalIntegrable_of_continuousOn_Icc_real hab
          ((hg'c.mul hEc.continuousOn).norm)
      · exact intervalIntegrable_of_continuousOn_Icc_real hab (hg'c.norm)
      · intro t ht
        simp only [hEdef]
        rw [norm_mul, norm_phase, mul_one]
    have hdiv : (‖A b‖ + ‖A a‖) / lam = ‖A b‖ / lam + ‖A a‖ / lam := add_div _ _ _
    linarith [h1, h2, h3, h4, h5, hgb, hga, hdiv]
  -- final constant
  have h6 : 0 ≤ ∫ x in a..b, ‖deriv A x‖ :=
    intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
  have h7 : (‖A b‖ + ‖A a‖) / lam + (∫ t in a..b, ‖g' t‖) ≤
      4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖deriv A t‖) / lam := by
    have hstep1 : (‖A b‖ + ‖A a‖) / lam + (∫ t in a..b, ‖g' t‖) ≤
        (‖A b‖ + ‖A a‖) / lam + ((∫ t in a..b, ‖deriv A t‖) / lam +
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * (2 / lam)) := by linarith [hInt_g']
    have hstep2 : (‖A b‖ + ‖A a‖) / lam + ((∫ t in a..b, ‖deriv A t‖) / lam +
        (‖A a‖ + ∫ x in a..b, ‖deriv A x‖) * (2 / lam)) =
        (‖A b‖ + 3 * ‖A a‖ + 3 * (∫ t in a..b, ‖deriv A t‖)) / lam := by
      rw [add_div, add_div, add_div, mul_div_assoc, mul_div_assoc]
      ring
    have hstep3 : (‖A b‖ + 3 * ‖A a‖ + 3 * (∫ t in a..b, ‖deriv A t‖)) / lam ≤
        4 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖deriv A t‖) / lam :=
      (div_le_div_iff_of_pos_right hlam).mpr (by
        linarith [h6, norm_nonneg (A a), norm_nonneg (A b)])
    rw [hstep2] at hstep1
    exact hstep1.trans hstep3
  exact hfinal.trans h7

/-- Second derivative test. If `φ'' ≥ μ > 0` on `[a,b]`, then `∫ A e^{iφ}` is at
most `32/√μ` times the amplitude budget. -/
theorem secondDerivTest {φ : ℝ → ℝ} {A : ℝ → ℂ} {a b mu : ℝ}
    (hab : a ≤ b) (hmu : 0 < mu)
    (hφ : ContDiff ℝ 2 φ)
    (hbound : ∀ t ∈ Set.Icc a b, mu ≤ deriv (deriv φ) t)
    (hA : ContDiff ℝ 1 A) :
    ‖∫ t in a..b, A t * Complex.exp (Complex.I * φ t)‖ ≤
      32 * (‖A b‖ + ‖A a‖ + ∫ t in a..b, ‖deriv A t‖) / Real.sqrt mu := by
  have hφ1 : Continuous (deriv φ) := hφ.continuous_deriv (by norm_num)
  have hφ2 : Continuous (deriv (deriv φ)) :=
    (ContDiff.deriv' hφ).continuous_deriv (le_refl 1)
  have hAc : Continuous A := hA.continuous
  have hφ2d : ∀ t, DifferentiableAt ℝ (deriv φ) t :=
    fun t => (hφ.differentiable_deriv_two).differentiableAt
  have hδ : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu
  set E : ℝ → ℂ := fun t => Complex.exp (Complex.I * φ t) with hEdef
  have hEc : Continuous E := by
    apply Complex.continuous_exp.comp
    exact continuous_const.mul (continuous_ofReal.comp hφ.continuous)
  have hδsq : Real.sqrt mu * Real.sqrt mu = mu := Real.mul_self_sqrt (le_of_lt hmu)
  have hAEc : ContinuousOn (fun t => A t * E t) (Set.Icc a b) := hAc.continuousOn.mul hEc.continuousOn
  have hA1c : ContinuousOn (fun x => ‖deriv A x‖) (Set.Icc a b) :=
    (hA.continuous_deriv (le_refl 1)).norm.continuousOn
  -- the global amplitude budget
  set M : ℝ := ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ with hMdef
  have hM : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ M := fun t ht => norm_le_deriv_budget hA t ht
  have hMnn : 0 ≤ M := by
    have h6 : 0 ≤ ∫ x in a..b, ‖deriv A x‖ :=
      intervalIntegral.integral_nonneg hab (fun x _ => norm_nonneg _)
    linarith [norm_nonneg (A a), h6]
  -- sub-interval ∫‖A'‖ ≤ ∫_a^b‖A'‖
  have hMint : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b →
      (∫ t in p..q, ‖deriv A t‖) ≤ ∫ t in a..b, ‖deriv A t‖ := by
    intro p q hap hpq hqb
    have h1 := intervalIntegral.integral_add_adjacent_intervals (f := fun x => ‖deriv A x‖)
      (intervalIntegrable_of_continuousOn_Icc_real hap
        (hA1c.mono (Set.Icc_subset_Icc (le_refl a) (hpq.trans hqb))))
      (intervalIntegrable_of_continuousOn_Icc_real hpq
        (hA1c.mono (Set.Icc_subset_Icc hap hqb)))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (f := fun x => ‖deriv A x‖)
      (intervalIntegrable_of_continuousOn_Icc_real hpq
        (hA1c.mono (Set.Icc_subset_Icc hap hqb)))
      (intervalIntegrable_of_continuousOn_Icc_real hqb
        (hA1c.mono (Set.Icc_subset_Icc (hap.trans hpq) (le_refl b))))
    have h3 := intervalIntegral.integral_add_adjacent_intervals (f := fun x => ‖deriv A x‖)
      (intervalIntegrable_of_continuousOn_Icc_real hap
        (hA1c.mono (Set.Icc_subset_Icc (le_refl a) (hpq.trans hqb))))
      (intervalIntegrable_of_continuousOn_Icc_real (hpq.trans hqb)
        (hA1c.mono (Set.Icc_subset_Icc hap (le_refl b))))
    have n1 : 0 ≤ ∫ t in a..p, ‖deriv A t‖ :=
      intervalIntegral.integral_nonneg hap (fun x _ => norm_nonneg _)
    have n2 : 0 ≤ ∫ t in q..b, ‖deriv A t‖ :=
      intervalIntegral.integral_nonneg hqb (fun x _ => norm_nonneg _)
    linarith
  -- φ' growth from the left and right via FTC
  have hφ'lo : ∀ {p t : ℝ}, a ≤ p → p ≤ t → t ≤ b →
      mu * (t - p) ≤ deriv φ t - deriv φ p := by
    intro p t hap hpt htb
    have hftc : ∫ x in p..t, deriv (deriv φ) x = deriv φ t - deriv φ p :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => (hφ2d x))
        (intervalIntegrable_of_continuousOn_Icc_real hpt
          (hφ2.continuousOn.mono (Set.Icc_subset_Icc hap htb)))
    have hmono : (∫ x in p..t, mu) ≤ ∫ x in p..t, deriv (deriv φ) x := by
      apply intervalIntegral.integral_mono_on hpt intervalIntegrable_const
        (intervalIntegrable_of_continuousOn_Icc_real hpt
          (hφ2.continuousOn.mono (Set.Icc_subset_Icc hap htb)))
      intro x hx
      exact hbound x (Set.Icc_subset_Icc hap htb hx)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [hftc, hmono]
  have hφ'hi : ∀ {q t : ℝ}, a ≤ t → t ≤ q → q ≤ b →
      mu * (q - t) ≤ deriv φ q - deriv φ t := by
    intro q t hat htq hqb
    have hftc : ∫ x in t..q, deriv (deriv φ) x = deriv φ q - deriv φ t :=
      intervalIntegral.integral_deriv_eq_sub (fun x _ => (hφ2d x))
        (intervalIntegrable_of_continuousOn_Icc_real htq
          (hφ2.continuousOn.mono (Set.Icc_subset_Icc hat hqb)))
    have hmono : (∫ x in t..q, mu) ≤ ∫ x in t..q, deriv (deriv φ) x := by
      apply intervalIntegral.integral_mono_on htq intervalIntegrable_const
        (intervalIntegrable_of_continuousOn_Icc_real htq
          (hφ2.continuousOn.mono (Set.Icc_subset_Icc hat hqb)))
      intro x hx
      exact hbound x (Set.Icc_subset_Icc hat hqb hx)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    linarith [hftc, hmono]
  -- Case A engine: φ'(p) ≥ 0
  have caseA : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → 0 ≤ deriv φ p →
      ‖∫ t in p..q, A t * E t‖ ≤ 13 * M / Real.sqrt mu := by
    intro p q hap hpq hqb hp0
    have hpqc : Set.Icc p q ⊆ Set.Icc a b := Set.Icc_subset_Icc hap hqb
    by_cases hshort : q ≤ p + 1 / Real.sqrt mu
    · have h1 : ‖∫ t in p..q, A t * E t‖ ≤ M * (q - p) := by
        apply norm_integral_le_const_mul_length hpq (fun t ht => hM t (hpqc ht))
      have h2 : M * (q - p) ≤ M * (1 / Real.sqrt mu) := by
        apply mul_le_mul_of_nonneg_left _ hMnn
        linarith [hshort]
      have h3 : M * (1 / Real.sqrt mu) = M / Real.sqrt mu := by ring
      have h4 : M / Real.sqrt mu ≤ 13 * M / Real.sqrt mu := by
        apply div_le_div_of_nonneg_right
        · linarith [hMnn]
        · exact le_of_lt hδ
      linarith [h1, h2, h3 ▸ h4]
    · have hshort : p + 1 / Real.sqrt mu < q := lt_of_not_ge hshort
      set u := p + 1 / Real.sqrt mu with hudef
      have hpu : p ≤ u := by rw [hudef]; linarith [hδ, one_div_pos.mpr hδ]
      have huq : u ≤ q := le_of_lt hshort
      have hsplit : ∫ t in p..q, A t * E t =
          (∫ t in p..u, A t * E t) + ∫ t in u..q, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_continuousOn_Icc hpu (hAEc.mono (Set.Icc_subset_Icc hap (huq.trans hqb))))
          (intervalIntegrable_of_continuousOn_Icc huq (hAEc.mono (Set.Icc_subset_Icc (hap.trans hpu) hqb)))]
      rw [hsplit]
      have hleft : ‖∫ t in p..u, A t * E t‖ ≤ M * (u - p) :=
        norm_integral_le_const_mul_length hpu (fun t ht => hM t (hpqc ⟨ht.1, ht.2.trans huq⟩))
      have hright : ‖∫ t in u..q, A t * E t‖ ≤
          4 * (‖A q‖ + ‖A u‖ + ∫ t in u..q, ‖deriv A t‖) / Real.sqrt mu := by
        apply firstDerivTest huq hδ hφ
        · intro t ht
          exact le_of_lt (lt_of_lt_of_le hmu (hbound t (hpqc ⟨hpu.trans ht.1, ht.2⟩)))
        · intro t ht
          have h1 : mu * (t - p) ≤ deriv φ t - deriv φ p :=
            hφ'lo hap (hpu.trans ht.1) (hpqc ⟨hpu.trans ht.1, ht.2⟩).2
          have h2 : mu * (t - p) ≥ mu * (u - p) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hmu)
            linarith [ht.1]
          have h3 : mu * (u - p) = Real.sqrt mu := by
            rw [hudef, show p + 1 / Real.sqrt mu - p = 1 / Real.sqrt mu by ring, mul_one_div,
              div_eq_iff (ne_of_gt hδ)]
            exact hδsq.symm
          have h4 : deriv φ t ≥ Real.sqrt mu := by linarith [h1, h2, h3, hp0]
          rw [abs_of_nonneg (le_of_lt (lt_of_lt_of_le hδ h4))]
          exact h4
        · exact hA
      -- assemble
      have hAq : ‖A q‖ ≤ M := hM q (hpqc ⟨hpq, le_refl q⟩)
      have hAu : ‖A u‖ ≤ M := hM u (hpqc ⟨hpu, huq⟩)
      have hint : (∫ t in u..q, ‖deriv A t‖) ≤ M := by
        have h5 : (∫ t in u..q, ‖deriv A t‖) ≤ ∫ t in a..b, ‖deriv A t‖ :=
          hMint (hap.trans hpu) huq hqb
        have h6 : 0 ≤ ‖A a‖ := norm_nonneg _
        linarith [h5, h6]
      have h7 : M * (u - p) = M / Real.sqrt mu := by rw [hudef]; ring
      have h8 : 4 * (‖A q‖ + ‖A u‖ + ∫ t in u..q, ‖deriv A t‖) / Real.sqrt mu ≤
          12 * M / Real.sqrt mu := by
        apply div_le_div_of_nonneg_right
        · linarith [hAq, hAu, hint]
        · exact le_of_lt hδ
      exact (norm_add_le _ _).trans (by
        have hsum : M / Real.sqrt mu + 12 * M / Real.sqrt mu = 13 * M / Real.sqrt mu := by
          rw [← add_div]; ring
        linarith [hleft, hright, h7, h8, hMnn, hsum])
  -- Case B engine: φ'(q) ≤ 0
  have caseB : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q ≤ b → deriv φ q ≤ 0 →
      ‖∫ t in p..q, A t * E t‖ ≤ 13 * M / Real.sqrt mu := by
    intro p q hap hpq hqb hq0
    have hpqc : Set.Icc p q ⊆ Set.Icc a b := Set.Icc_subset_Icc hap hqb
    by_cases hshort : q ≤ p + 1 / Real.sqrt mu
    · have h1 : ‖∫ t in p..q, A t * E t‖ ≤ M * (q - p) := by
        apply norm_integral_le_const_mul_length hpq (fun t ht => hM t (hpqc ht))
      have h2 : M * (q - p) ≤ M * (1 / Real.sqrt mu) := by
        apply mul_le_mul_of_nonneg_left _ hMnn
        linarith [hshort]
      have h3 : M * (1 / Real.sqrt mu) = M / Real.sqrt mu := by ring
      have h4 : M / Real.sqrt mu ≤ 13 * M / Real.sqrt mu := by
        apply div_le_div_of_nonneg_right
        · linarith [hMnn]
        · exact le_of_lt hδ
      linarith [h1, h2, h3 ▸ h4]
    · have hshort : p + 1 / Real.sqrt mu < q := lt_of_not_ge hshort
      set u := q - 1 / Real.sqrt mu with hudef
      have huq : u ≤ q := by rw [hudef]; linarith [hδ, one_div_pos.mpr hδ]
      have hpu : p ≤ u := by linarith [hshort, hudef, hδ, one_div_pos.mpr hδ]
      have hsplit : ∫ t in p..q, A t * E t =
          (∫ t in p..u, A t * E t) + ∫ t in u..q, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_continuousOn_Icc hpu (hAEc.mono (Set.Icc_subset_Icc hap (huq.trans hqb))))
          (intervalIntegrable_of_continuousOn_Icc huq (hAEc.mono (Set.Icc_subset_Icc (hap.trans hpu) hqb)))]
      rw [hsplit]
      have hright : ‖∫ t in u..q, A t * E t‖ ≤ M * (q - u) :=
        norm_integral_le_const_mul_length huq (fun t ht => hM t (hpqc ⟨hpu.trans ht.1, ht.2⟩))
      have hleft : ‖∫ t in p..u, A t * E t‖ ≤
          4 * (‖A u‖ + ‖A p‖ + ∫ t in p..u, ‖deriv A t‖) / Real.sqrt mu := by
        apply firstDerivTest hpu hδ hφ
        · intro t ht
          exact le_of_lt (lt_of_lt_of_le hmu (hbound t (hpqc ⟨ht.1, ht.2.trans huq⟩)))
        · intro t ht
          have h1 : mu * (q - t) ≤ deriv φ q - deriv φ t :=
            hφ'hi (hpqc ⟨ht.1, ht.2.trans huq⟩).1 (ht.2.trans huq) hqb
          have h2 : mu * (q - t) ≥ mu * (q - u) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hmu)
            linarith [ht.2]
          have h3 : mu * (q - u) = Real.sqrt mu := by
            rw [hudef, show q - (q - 1 / Real.sqrt mu) = 1 / Real.sqrt mu by ring, mul_one_div,
              div_eq_iff (ne_of_gt hδ)]
            exact hδsq.symm
          have h4 : deriv φ t ≤ -Real.sqrt mu := by linarith [h1, h2, h3, hq0]
          have h5 : deriv φ t ≤ 0 := by linarith [h4, hδ]
          rw [abs_of_nonpos h5]
          linarith [h4]
        · exact hA
      have hAp : ‖A p‖ ≤ M := hM p (hpqc ⟨le_refl p, hpq⟩)
      have hAu : ‖A u‖ ≤ M := hM u (hpqc ⟨hpu, huq⟩)
      have hint : (∫ t in p..u, ‖deriv A t‖) ≤ M := by
        have h5 : (∫ t in p..u, ‖deriv A t‖) ≤ ∫ t in a..b, ‖deriv A t‖ :=
          hMint hap hpu (huq.trans hqb)
        have h6 : 0 ≤ ‖A a‖ := norm_nonneg _
        linarith [h5, h6]
      have h7 : M * (q - u) = M / Real.sqrt mu := by rw [hudef]; ring
      have h8 : 4 * (‖A u‖ + ‖A p‖ + ∫ t in p..u, ‖deriv A t‖) / Real.sqrt mu ≤
          12 * M / Real.sqrt mu := by
        apply div_le_div_of_nonneg_right
        · linarith [hAp, hAu, hint]
        · exact le_of_lt hδ
      exact (norm_add_le _ _).trans (by
        have hsum : M / Real.sqrt mu + 12 * M / Real.sqrt mu = 13 * M / Real.sqrt mu := by
          rw [← add_div]; ring
        linarith [hleft, hright, h7, h8, hMnn, hsum])
  -- main case split
  set B : ℝ := ‖A b‖ + ‖A a‖ + ∫ x in a..b, ‖deriv A x‖ with hBdef
  have hMB : M ≤ B := by
    have h6 : 0 ≤ ‖A b‖ := norm_nonneg _
    linarith [h6]
  by_cases h1 : 0 ≤ deriv φ a
  · have h := caseA (le_refl a) hab (le_refl b) h1
    -- 13 * M ≤ 32 * B
    have h13 : 13 * M / Real.sqrt mu ≤ 32 * B / Real.sqrt mu := by
      apply div_le_div_of_nonneg_right
      · have h2 : 13 * M ≤ 32 * B := by linarith [hMB, hMnn]
        exact h2
      · exact le_of_lt hδ
    exact h.trans h13
  · have h1 : deriv φ a < 0 := lt_of_not_ge h1
    by_cases h2 : deriv φ b ≤ 0
    · have h := caseB (le_refl a) hab (le_refl b) h2
      have h13 : 13 * M / Real.sqrt mu ≤ 32 * B / Real.sqrt mu := by
        apply div_le_div_of_nonneg_right
        · linarith [hMB, hMnn]
        · exact le_of_lt hδ
      exact h.trans h13
    · have h2 : 0 < deriv φ b := lt_of_not_ge h2
      -- IVT zero c
      have hivt := intermediate_value_Icc hab hφ1.continuousOn
      have h0in : (0 : ℝ) ∈ Set.Icc (deriv φ a) (deriv φ b) := ⟨le_of_lt h1, le_of_lt h2⟩
      obtain ⟨c, hc, hfc⟩ := hivt h0in
      have hfc0 : deriv φ c = 0 := hfc
      have hsplit : ∫ t in a..b, A t * E t = (∫ t in a..c, A t * E t) + ∫ t in c..b, A t * E t := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_of_continuousOn_Icc hc.1 (hAEc.mono (Set.Icc_subset_Icc (le_refl a) hc.2)))
          (intervalIntegrable_of_continuousOn_Icc hc.2 (hAEc.mono (Set.Icc_subset_Icc hc.1 (le_refl b))))]
      rw [hsplit]
      have hleft := caseB (le_refl a) hc.1 hc.2 (le_of_eq hfc0)
      have hright := caseA hc.1 hc.2 (le_refl b) (le_of_eq hfc0.symm)
      have h26 : 13 * M / Real.sqrt mu + 13 * M / Real.sqrt mu ≤ 32 * B / Real.sqrt mu := by
        have h3 : 13 * M / Real.sqrt mu + 13 * M / Real.sqrt mu = 26 * M / Real.sqrt mu := by ring
        rw [h3]
        apply div_le_div_of_nonneg_right
        · linarith [hMB, hMnn]
        · exact le_of_lt hδ
      exact (norm_add_le _ _).trans (by linarith [hleft, hright, h26])

end RHTower

namespace RHTower


/-- **van der Corput first-derivative test, increasing derivative.**  For a real phase `g` with
derivative `g'` and second derivative `g''` on `[a,b]`, with `g'` bounded below by `lam > 0` and
nondecreasing (`g'' ≥ 0`), the oscillatory integral obeys `‖∫ exp(i·g)‖ ≤ 2/lam`. -/
theorem norm_integral_cexp_ofReal_mul_I_le_mono
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hpos : ∀ x ∈ Set.uIcc a b, lam ≤ g' x)
    (hmono : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 2 / lam := by
  have hg'pos : ∀ x ∈ Set.uIcc a b, 0 < g' x := fun x hx => lt_of_lt_of_le hlam (hpos x hx)
  have hg'ne : ∀ x ∈ Set.uIcc a b, (g' x : ℂ) * I ≠ 0 := fun x hx =>
    mul_ne_zero (by exact_mod_cast (hg'pos x hx).ne') I_ne_zero
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  set V : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) with hVdef
  set V' : ℝ → ℂ := fun t => Complex.exp ((g t : ℂ) * I) * ((g' t : ℂ) * I) with hV'def
  set U : ℝ → ℂ := fun t => ((g' t : ℂ) * I)⁻¹ with hUdef
  set U' : ℝ → ℂ := fun t => -(((g'' t : ℂ) * I) / ((g' t : ℂ) * I) ^ 2) with hU'def
  have hVderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt V (V' x) x := fun x hx =>
    (((hg x hx).ofReal_comp).mul_const I).cexp
  have hUderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt U (U' x) x := by
    intro x hx
    have hw : HasDerivAt (fun t => (g' t : ℂ) * I) ((g'' x : ℂ) * I) x :=
      ((hg' x hx).ofReal_comp).mul_const I
    have h2 := (hasDerivAt_inv (hg'ne x hx)).comp x hw
    rw [hU'def, hUdef]
    change HasDerivAt (fun t : ℝ => ((g' t : ℂ) * I)⁻¹)
      (-(((g'' x : ℂ) * I) / ((g' x : ℂ) * I) ^ 2)) x
    have hfun :
        (fun t : ℝ => ((g' t : ℂ) * I)⁻¹) =
          (fun y : ℂ => y⁻¹) ∘ fun t : ℝ => (g' t : ℂ) * I := rfl
    have hcoeff :
        -(((g'' x : ℂ) * I) / ((g' x : ℂ) * I) ^ 2) =
          -(((g' x : ℂ) * I) ^ 2)⁻¹ * ((g'' x : ℂ) * I) := by
      rw [div_eq_mul_inv]
      ring
    rw [hfun, hcoeff]
    exact h2
  have hVnorm : ∀ t, ‖V t‖ = 1 := by intro t; rw [hVdef]; simp [Complex.norm_exp]
  have hUnorm : ∀ x ∈ Set.uIcc a b, ‖U x‖ = (g' x)⁻¹ := by
    intro x hx; rw [hUdef, norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hg'pos x hx)]
  have hU'norm : ∀ x ∈ Set.uIcc a b, ‖U' x‖ = g'' x / (g' x) ^ 2 := by
    intro x hx; rw [hU'def, norm_neg, norm_div, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hmono x hx)]
    rw [norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hg'pos x hx)]
  have hVcont : ContinuousOn V (Set.uIcc a b) := by
    rw [hVdef]
    exact Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)
  have hU'cont : ContinuousOn U' (Set.uIcc a b) := by
    rw [hU'def]
    refine ContinuousOn.neg (ContinuousOn.div
      ((continuous_ofReal.comp_continuousOn hg''c).mul continuousOn_const)
      (((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const).pow 2)
      (fun x hx => pow_ne_zero _ (hg'ne x hx)))
  have hV'cont : ContinuousOn V' (Set.uIcc a b) := by
    rw [hV'def]
    exact (Complex.continuous_exp.comp_continuousOn
      ((continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)).mul
      ((continuous_ofReal.comp_continuousOn hg'c).mul continuousOn_const)
  have hV'int : IntervalIntegrable V' volume a b := hV'cont.intervalIntegrable
  have hU'int : IntervalIntegrable U' volume a b := hU'cont.intervalIntegrable
  have hVint : IntervalIntegrable V volume a b := hVcont.intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hUderiv hVderiv hU'int hV'int
  have hUV' : ∀ x ∈ Set.uIcc a b, U' x * V x + U x * V' x = U' x * V x + V x := by
    intro x hx
    have hval : U x * V' x = V x := by
      simp only [hUdef, hV'def, hVdef]
      rw [mul_comm (Complex.exp _) ((g' x : ℂ) * I), ← mul_assoc,
        inv_mul_cancel₀ (hg'ne x hx), one_mul]
    rw [hval]
  rw [intervalIntegral.integral_congr hUV'] at hibp
  have hUVint : IntervalIntegrable (fun x => U' x * V x) volume a b :=
    hU'int.mul_continuousOn hVcont
  rw [intervalIntegral.integral_add hUVint hVint] at hibp
  have hsplit : (∫ x in a..b, V x) = (U b * V b - U a * V a) - ∫ x in a..b, U' x * V x := by
    linear_combination hibp
  have hbdry : ‖U b * V b - U a * V a‖ ≤ (g' a)⁻¹ + (g' b)⁻¹ := by
    calc ‖U b * V b - U a * V a‖ ≤ ‖U b * V b‖ + ‖U a * V a‖ := norm_sub_le _ _
      _ = (g' b)⁻¹ + (g' a)⁻¹ := by
          rw [norm_mul, norm_mul, hVnorm, hVnorm, mul_one, mul_one,
            hUnorm b Set.right_mem_uIcc, hUnorm a Set.left_mem_uIcc]
      _ = (g' a)⁻¹ + (g' b)⁻¹ := by ring
  have hFTCderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => -(g' t)⁻¹) (g'' x / (g' x) ^ 2) x := by
    intro x hx
    have hi := ((hg' x hx).inv (hg'pos x hx).ne').neg
    have hfun : (fun t : ℝ => -(g' t)⁻¹) = -g'⁻¹ := by
      funext t
      rfl
    have hcoeff : g'' x / (g' x) ^ 2 = -(-g'' x / (g' x) ^ 2) := by ring
    rw [hfun, hcoeff]
    exact hi
  have hFTCint : IntervalIntegrable (fun t => g'' t / (g' t) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div hg''c (hg'c.pow 2) (fun x hx => pow_ne_zero _ (hg'pos x hx).ne')
  have hintUV : ‖∫ x in a..b, U' x * V x‖ ≤ (g' a)⁻¹ - (g' b)⁻¹ := by
    calc ‖∫ x in a..b, U' x * V x‖
        ≤ ∫ x in a..b, ‖U' x * V x‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ x in a..b, g'' x / (g' x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x hx
          show ‖U' x * V x‖ = g'' x / (g' x) ^ 2
          rw [norm_mul, hVnorm, mul_one, hU'norm x hx]
      _ = (g' a)⁻¹ - (g' b)⁻¹ := by
          have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hFTCderiv hFTCint
          linarith [hftc]
  rw [hsplit]
  calc ‖(U b * V b - U a * V a) - ∫ x in a..b, U' x * V x‖
      ≤ ‖U b * V b - U a * V a‖ + ‖∫ x in a..b, U' x * V x‖ := norm_sub_le _ _
    _ ≤ ((g' a)⁻¹ + (g' b)⁻¹) + ((g' a)⁻¹ - (g' b)⁻¹) := add_le_add hbdry hintUV
    _ = 2 * (g' a)⁻¹ := by ring
    _ ≤ 2 / lam := by rw [div_eq_mul_inv]; gcongr; exact hpos a Set.left_mem_uIcc


end RHTower

namespace RHTower

/-- An antitone nonnegative weight is bounded by its left value: for `w` with derivative `w' ≤ 0`
on `[a,b]`, `w x ≤ w a` for every `x` in the interval.  Proven by integrating `w' ≤ 0` from `a`
to `x`. -/
theorem weight_le_left_of_deriv_nonpos {a b : ℝ} (hab : a ≤ b) {w w' : ℝ → ℝ}
    (hw : ∀ x ∈ Set.uIcc a b, HasDerivAt w (w' x) x)
    (hw'c : ContinuousOn w' (Set.uIcc a b))
    (hwanti : ∀ x ∈ Set.uIcc a b, w' x ≤ 0) :
    ∀ x ∈ Set.uIcc a b, w x ≤ w a := by
  intro x hx
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
  have hsub : Set.uIcc a x ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hx
  have hint : IntervalIntegrable w' volume a x := (hw'c.mono hsub).intervalIntegrable
  have hftc : ∫ t in a..x, w' t = w x - w a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hw t (hsub ht)) hint
  have hnp : ∫ t in a..x, w' t ≤ 0 := by
    have hm := intervalIntegral.integral_mono_on hxIcc.1 hint
      (intervalIntegrable_const (c := (0 : ℝ)))
      (fun t ht => hwanti t (hsub (by rw [Set.uIcc_of_le hxIcc.1]; exact ht)))
    simpa using hm
  linarith [hftc, hnp]

end RHTower
