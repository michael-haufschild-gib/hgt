import GaloisForLFunctions.HTGeometry.KleinGordonSecondOrderDuhamel

/-!
# Low frequencies, where the propagators are analytic in time

The ill-posedness of the inverse problem lives entirely at high frequency: the damping `⟨ξ⟩⁻¹` that
hides a perturbation from the field is small only when `⟨ξ⟩` is large. Below a fixed frequency the
picture reverses, and this file supplies the estimates that make it quantitative.

Cutting to `‖ξ‖ ≤ R` makes the two propagator symbols agree with their Taylor polynomials to the
expected order, with constants that are explicit in `R`:

`‖(cos(τ⟨D⟩) − 1)P_R‖ ≤ τ²(1+R²)/2`,   `‖(sin(τ⟨D⟩)/⟨D⟩ − τ)P_R‖ ≤ |τ|³(1+R²)/6`.

Both come from the scalar estimates `|cos a − 1| ≤ a²/2` and `|sin a − a| ≤ |a|³/6`; the second is
not in mathlib and is proved here by integrating the first.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-! ## Two scalar Taylor bounds -/

theorem abs_cos_sub_one_le (x : ℝ) : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have := Real.one_sub_sq_div_two_le_cos (x := x)
    linarith
  · have := Real.cos_le_one x
    have hsq : (0 : ℝ) ≤ x ^ 2 / 2 := by positivity
    linarith

private theorem abs_sin_sub_self_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    |Real.sin y - y| ≤ y ^ 3 / 6 := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) y,
      HasDerivAt (fun u : ℝ => Real.sin u - u) (Real.cos t - 1) t := fun t _ =>
    (Real.hasDerivAt_sin t).sub (hasDerivAt_id t)
  have hint : IntervalIntegrable (fun t : ℝ => Real.cos t - 1) volume 0 y :=
    (Real.continuous_cos.sub continuous_const).intervalIntegrable 0 y
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [Real.sin_zero, sub_zero, sub_zero] at hFTC
  have habs : IntervalIntegrable (fun t : ℝ => |Real.cos t - 1|) volume 0 y :=
    ((Real.continuous_cos.sub continuous_const).abs).intervalIntegrable 0 y
  have hquad : IntervalIntegrable (fun t : ℝ => t ^ 2 / 2) volume 0 y :=
    ((continuous_pow 2).div_const 2).intervalIntegrable 0 y
  have h1 : ‖∫ t in (0 : ℝ)..y, (Real.cos t - 1)‖ ≤ ∫ t in (0 : ℝ)..y, ‖Real.cos t - 1‖ :=
    intervalIntegral.norm_integral_le_integral_norm hy
  have h2 : (∫ t in (0 : ℝ)..y, ‖Real.cos t - 1‖) ≤ ∫ t in (0 : ℝ)..y, t ^ 2 / 2 := by
    refine intervalIntegral.integral_mono_on hy habs hquad fun t _ => ?_
    rw [Real.norm_eq_abs]
    exact abs_cos_sub_one_le t
  have hval : (∫ t in (0 : ℝ)..y, t ^ 2 / 2) = y ^ 3 / 6 := by
    rw [intervalIntegral.integral_div, integral_pow]
    norm_num
    ring
  rw [hFTC, Real.norm_eq_abs] at h1
  calc |Real.sin y - y| ≤ ∫ t in (0 : ℝ)..y, ‖Real.cos t - 1‖ := h1
    _ ≤ ∫ t in (0 : ℝ)..y, t ^ 2 / 2 := h2
    _ = y ^ 3 / 6 := hval

/-- **`|sin a − a| ≤ |a|³/6`**, by integrating `|cos t − 1| ≤ t²/2`. -/
theorem abs_sin_sub_self_le (x : ℝ) : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
  rcases le_total (0 : ℝ) x with hx | hx
  · rw [abs_of_nonneg hx]
    exact abs_sin_sub_self_le_of_nonneg hx
  · have h := abs_sin_sub_self_le_of_nonneg (y := -x) (by linarith)
    rw [Real.sin_neg, neg_sub_neg] at h
    rw [abs_of_nonpos hx, ← abs_sub_comm]
    exact h

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The low-pass projection -/

/-- The symbol of the low-pass projection: one below frequency `R`, zero above. -/
def kgLowPass (R : ℝ) (ξ : E) : ℂ := if ‖ξ‖ ≤ R then 1 else 0

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgLowPass (R : ℝ) : Measurable (kgLowPass (E := E) R) :=
  Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
    measurable_const measurable_const

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgLowPass_le (R : ℝ) (ξ : E) : ‖kgLowPass R ξ‖ ≤ 1 := by
  rw [kgLowPass]
  split <;> simp

/-- **The low-pass projection**: the Fourier multiplier that keeps the frequencies below `R`. -/
def kgLowPassOp (R : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  fourierMulCLM (measurable_kgLowPass (E := E) R) zero_le_one (norm_kgLowPass_le R)

theorem kgLowPassOp_eq (R : ℝ) : kgLowPassOp (E := E) R
    = fourierMulCLM (measurable_kgLowPass (E := E) R) zero_le_one (norm_kgLowPass_le R) := rfl

theorem norm_kgLowPassOp_le (R : ℝ) : ‖kgLowPassOp (E := E) R‖ ≤ 1 :=
  norm_fourierMulCLM_le _ _ _

theorem norm_kgLowPassOp_apply_le (R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgLowPassOp R x‖ ≤ ‖x‖ := by
  have h := (kgLowPassOp (E := E) R).le_of_opNorm_le (norm_kgLowPassOp_le R) x
  rwa [one_mul] at h

/-! ## The propagators are Taylor-accurate below a fixed frequency -/

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem kgFreq_sq_le {R : ℝ} {ξ : E} (hξ : ‖ξ‖ ≤ R) : kgFreq ξ ^ 2 ≤ 1 + R ^ 2 := by
  rw [kgFreq, Real.sq_sqrt (by positivity)]
  have h : ‖ξ‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg ξ
    nlinarith
  linarith

/-- The symbol of `cos(τ⟨D⟩) − 1`, cut to the frequencies below `R`. -/
def kgCosDefectLow (τ R : ℝ) (ξ : E) : ℂ := (kgCosSymbol τ ξ - 1) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgCosDefectLow (τ R : ℝ) : Measurable (kgCosDefectLow (E := E) τ R) :=
  ((measurable_kgCosSymbol τ).sub measurable_const).mul (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgCosDefectLow_le (τ R : ℝ) (ξ : E) :
    ‖kgCosDefectLow τ R ξ‖ ≤ τ ^ 2 * (1 + R ^ 2) / 2 := by
  have hB0 : (0 : ℝ) ≤ τ ^ 2 * (1 + R ^ 2) / 2 := by positivity
  rw [kgCosDefectLow, kgLowPass]
  split
  · rename_i hξ
    rw [mul_one, kgCosSymbol, show ((1 : ℂ)) = ((1 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos (τ * kgFreq ξ) - 1| ≤ (τ * kgFreq ξ) ^ 2 / 2 :=
      abs_cos_sub_one_le _
    have h2 : (τ * kgFreq ξ) ^ 2 / 2 = τ ^ 2 * kgFreq ξ ^ 2 / 2 := by ring
    have h3 : kgFreq ξ ^ 2 ≤ 1 + R ^ 2 := kgFreq_sq_le hξ
    have h4 : τ ^ 2 * kgFreq ξ ^ 2 / 2 ≤ τ ^ 2 * (1 + R ^ 2) / 2 := by
      have : (0 : ℝ) ≤ τ ^ 2 := sq_nonneg τ
      nlinarith
    rw [h2] at h1
    linarith
  · simpa using hB0

/-- **The cosine propagator is the identity to second order, below a fixed frequency.** -/
theorem norm_kgCosOp_lowPass_sub_le (τ R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgCosOp τ (kgLowPassOp R x) - kgLowPassOp R x‖ ≤ τ ^ 2 * (1 + R ^ 2) / 2 * ‖x‖ := by
  have hB0 : (0 : ℝ) ≤ τ ^ 2 * (1 + R ^ 2) / 2 := by positivity
  have hprod : Measurable fun ξ : E => kgCosSymbol τ ξ * kgLowPass R ξ :=
    (measurable_kgCosSymbol τ).mul (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgCosSymbol τ ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgCosSymbol_le τ ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgCosSymbol τ ξ), norm_nonneg (kgLowPass R ξ)]
  have hcomp : (kgCosOp (E := E) τ).comp (kgLowPassOp R)
      = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgCosOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Filter.Eventually.of_forall fun _ => rfl)
  have hdiff : fourierMulCLM (measurable_kgCosDefectLow (E := E) τ R) hB0
      (norm_kgCosDefectLow_le τ R)
      = fourierMulCLM hprod zero_le_one hprodb - kgLowPassOp R := by
    rw [kgLowPassOp_eq]
    refine fourierMulCLM_sub _ _ _ zero_le_one hprodb zero_le_one (norm_kgLowPass_le R) hB0
      (norm_kgCosDefectLow_le τ R) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [kgCosDefectLow]
    ring
  have hval : kgCosOp (E := E) τ (kgLowPassOp R x) - kgLowPassOp R x
      = fourierMulCLM (measurable_kgCosDefectLow (E := E) τ R) hB0
        (norm_kgCosDefectLow_le τ R) x := by
    rw [hdiff, sub_apply, ← ContinuousLinearMap.comp_apply, hcomp]
  rw [hval]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_fourierMulCLM_le _ _ _) x

/-- The symbol of `sin(τ⟨D⟩)/⟨D⟩ − τ`, cut to the frequencies below `R`. -/
def kgSinDefectLow (τ R : ℝ) (ξ : E) : ℂ := (kgSinOverFreq τ ξ - (τ : ℂ)) * kgLowPass R ξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem measurable_kgSinDefectLow (τ R : ℝ) : Measurable (kgSinDefectLow (E := E) τ R) :=
  ((measurable_kgSinOverFreq τ).sub measurable_const).mul (measurable_kgLowPass R)

omit [MeasurableSpace E] [BorelSpace E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_kgSinDefectLow_le (τ R : ℝ) (ξ : E) :
    ‖kgSinDefectLow τ R ξ‖ ≤ |τ| ^ 3 * (1 + R ^ 2) / 6 := by
  have hB0 : (0 : ℝ) ≤ |τ| ^ 3 * (1 + R ^ 2) / 6 := by positivity
  rw [kgSinDefectLow, kgLowPass]
  split
  · rename_i hξ
    have hpos := kgFreq_pos ξ
    rw [mul_one, kgSinOverFreq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hrw : Real.sin (τ * kgFreq ξ) / kgFreq ξ - τ
        = (Real.sin (τ * kgFreq ξ) - τ * kgFreq ξ) / kgFreq ξ := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    have h1 : |Real.sin (τ * kgFreq ξ) - τ * kgFreq ξ| ≤ |τ * kgFreq ξ| ^ 3 / 6 :=
      abs_sin_sub_self_le _
    have habs : |τ * kgFreq ξ| ^ 3 = |τ| ^ 3 * kgFreq ξ ^ 3 := by
      rw [abs_mul, abs_of_pos hpos, mul_pow]
    have h3 : kgFreq ξ ^ 2 ≤ 1 + R ^ 2 := kgFreq_sq_le hξ
    have hcube : |τ| ^ 3 * kgFreq ξ ^ 3 / 6 ≤ |τ| ^ 3 * (1 + R ^ 2) / 6 * kgFreq ξ := by
      have hfac : (0 : ℝ) ≤ |τ| ^ 3 * kgFreq ξ / 6 := by positivity
      have hmul := mul_le_mul_of_nonneg_left h3 hfac
      calc |τ| ^ 3 * kgFreq ξ ^ 3 / 6 = |τ| ^ 3 * kgFreq ξ / 6 * kgFreq ξ ^ 2 := by ring
        _ ≤ |τ| ^ 3 * kgFreq ξ / 6 * (1 + R ^ 2) := hmul
        _ = |τ| ^ 3 * (1 + R ^ 2) / 6 * kgFreq ξ := by ring
    rw [habs] at h1
    linarith
  · simpa using hB0

/-- **The half-order propagator is multiplication by the elapsed time to third order, below a fixed
frequency.** -/
theorem norm_kgSinFreqOp_lowPass_sub_smul_le (τ R : ℝ) (x : Lp ℂ 2 (volume : Measure E)) :
    ‖kgSinFreqOp τ (kgLowPassOp R x) - (τ : ℂ) • kgLowPassOp R x‖
      ≤ |τ| ^ 3 * (1 + R ^ 2) / 6 * ‖x‖ := by
  have hB0 : (0 : ℝ) ≤ |τ| ^ 3 * (1 + R ^ 2) / 6 := by positivity
  have hprod : Measurable fun ξ : E => kgSinOverFreq τ ξ * kgLowPass R ξ :=
    (measurable_kgSinOverFreq τ).mul (measurable_kgLowPass R)
  have hprodb : ∀ ξ : E, ‖kgSinOverFreq τ ξ * kgLowPass R ξ‖ ≤ 1 := by
    intro ξ
    rw [norm_mul]
    have h1 := norm_kgSinOverFreq_le τ ξ
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [norm_nonneg (kgSinOverFreq τ ξ), norm_nonneg (kgLowPass R ξ)]
  have hscal : Measurable fun ξ : E => (τ : ℂ) * kgLowPass R ξ :=
    measurable_const.mul (measurable_kgLowPass R)
  have hscalb : ∀ ξ : E, ‖(τ : ℂ) * kgLowPass R ξ‖ ≤ |τ| := by
    intro ξ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 := norm_kgLowPass_le R ξ
    nlinarith [abs_nonneg τ, norm_nonneg (kgLowPass R ξ)]
  have hcomp : (kgSinFreqOp (E := E) τ).comp (kgLowPassOp R)
      = fourierMulCLM hprod zero_le_one hprodb := by
    rw [kgSinFreqOp_eq, kgLowPassOp_eq]
    exact fourierMulCLM_comp _ _ hprod _ _ _ _ zero_le_one hprodb
      (Filter.Eventually.of_forall fun _ => rfl)
  have hsmul : fourierMulCLM hscal (abs_nonneg τ) hscalb = (τ : ℂ) • kgLowPassOp (E := E) R := by
    rw [kgLowPassOp_eq]
    exact fourierMulCLM_smul _ _ zero_le_one (norm_kgLowPass_le R) (abs_nonneg τ) hscalb
      (τ : ℂ) (Filter.Eventually.of_forall fun _ => rfl)
  have hdiff : fourierMulCLM (measurable_kgSinDefectLow (E := E) τ R) hB0
      (norm_kgSinDefectLow_le τ R)
      = fourierMulCLM hprod zero_le_one hprodb - fourierMulCLM hscal (abs_nonneg τ) hscalb := by
    refine fourierMulCLM_sub _ _ _ zero_le_one hprodb (abs_nonneg τ) hscalb hB0
      (norm_kgSinDefectLow_le τ R) (Filter.Eventually.of_forall fun ξ => ?_)
    rw [kgSinDefectLow]
    ring
  have hval : kgSinFreqOp (E := E) τ (kgLowPassOp R x) - (τ : ℂ) • kgLowPassOp R x
      = fourierMulCLM (measurable_kgSinDefectLow (E := E) τ R) hB0
        (norm_kgSinDefectLow_le τ R) x := by
    rw [hdiff, sub_apply, ← ContinuousLinearMap.comp_apply, hcomp, hsmul, smul_apply]
  rw [hval]
  exact ContinuousLinearMap.le_of_opNorm_le _ (norm_fourierMulCLM_le _ _ _) x

end GaloisForLFunctions.HTGeometry
