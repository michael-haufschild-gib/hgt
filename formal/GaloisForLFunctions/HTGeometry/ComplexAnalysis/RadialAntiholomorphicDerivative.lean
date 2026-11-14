import GaloisForLFunctions.HTGeometry.ComplexAnalysis.AntiholomorphicDifferential

/-!
# Antiholomorphic derivatives of radial profiles

For a real radial profile `φ(‖x‖²)`, the antiholomorphic differential is `φ'(‖x‖²)` times
the conjugate inner-product functional at `x`. Its operator norm is exactly
`|φ'(‖x‖²)| ‖x‖`. A holomorphic multiplier contributes its modulus but no derivative term.
-/

open Complex
open scoped InnerProductSpace ComplexConjugate

noncomputable section
namespace HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The conjugate-linear inner-product functional, viewed as real continuous linear. -/
def conjugateInnerFunctional (x : E) : E →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ x).restrictScalars ℝ)

theorem conjugateInnerFunctional_apply (x v : E) :
    conjugateInnerFunctional x v = conj (inner ℂ x v) := rfl

/-- The norm of the conjugate inner-product functional is the norm of its defining vector. -/
theorem norm_conjugateInnerFunctional (x : E) : ‖conjugateInnerFunctional x‖ = ‖x‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
    intro v
    rw [conjugateInnerFunctional_apply, norm_conj]
    exact norm_inner_le_norm x v
  · by_cases hx : x = 0
    · subst x
      simpa only [norm_zero] using norm_nonneg (conjugateInnerFunctional (0 : E))
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h := ContinuousLinearMap.le_opNorm (conjugateInnerFunctional x) x
    rw [conjugateInnerFunctional_apply, norm_conj, inner_self_eq_norm_sq_to_K,
      norm_pow, Complex.norm_real, norm_norm] at h
    nlinarith only [h, hp]

/-- Complexifying a real inner-product functional gives half its conjugate-linear component. -/
theorem antiholomorphicPart_ofReal_inner (c : ℝ) (x : E) :
    antiholomorphicPart (Complex.ofRealCLM.comp (c • innerSL ℝ x)) =
      ((c / 2 : ℝ) : ℂ) • conjugateInnerFunctional x := by
  ext v
  rw [antiholomorphicPart_apply]
  change ((↑(c * inner ℝ x v) : ℂ) + Complex.I * ↑(c * inner ℝ x (Complex.I • v))) / 2 =
    ↑(c / 2) * conj (inner ℂ x v)
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_smul_right]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Exact antiholomorphic differential of a profile in squared radius. -/
theorem dbarDifferential_radial_sq {φ : ℝ → ℝ} {φ' : ℝ} {x : E}
    (hφ : HasDerivAt φ φ' (‖x‖ ^ 2)) :
    dbarDifferential (fun y : E => (φ (‖y‖ ^ 2) : ℂ)) x =
      (φ' : ℂ) • conjugateInnerFunctional x := by
  have hsq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hr := hφ.comp_hasFDerivAt x hsq
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  rw [dbarDifferential, hc.fderiv]
  change antiholomorphicPart
    (Complex.ofRealCLM.comp (φ' • ((2 : ℝ) • innerSL ℝ x))) = _
  rw [smul_smul, antiholomorphicPart_ofReal_inner]
  congr 1
  push_cast
  ring

/-- Exact operator norm of the radial antiholomorphic differential. -/
theorem norm_dbarDifferential_radial_sq {φ : ℝ → ℝ} {φ' : ℝ} {x : E}
    (hφ : HasDerivAt φ φ' (‖x‖ ^ 2)) :
    ‖dbarDifferential (fun y : E => (φ (‖y‖ ^ 2) : ℂ)) x‖ = |φ'| * ‖x‖ := by
  rw [dbarDifferential_radial_sq hφ, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, norm_conjugateInnerFunctional]

/-- A holomorphic amplitude changes the radial defect only by its modulus. -/
theorem norm_dbarDifferential_holomorphic_radial_sq
    {h : E → ℂ} {φ : ℝ → ℝ} {φ' : ℝ} {x : E}
    (hh : DifferentiableAt ℂ h x) (hφ : HasDerivAt φ φ' (‖x‖ ^ 2)) :
    ‖dbarDifferential (fun y : E => h y * (φ (‖y‖ ^ 2) : ℂ)) x‖ =
      ‖h x‖ * (|φ'| * ‖x‖) := by
  have hr := hφ.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp x hr
  rw [dbarDifferential_holomorphic_mul hh hc.differentiableAt,
    norm_smul, norm_dbarDifferential_radial_sq hφ]

private theorem log_sq_half (r : ℝ) : Real.log (r ^ 2) / 2 = Real.log r := by
  rw [Real.log_pow]
  norm_num

private theorem hasDerivAt_logHalfProfile {χ : ℝ → ℝ} {χ' r : ℝ}
    (hr : 0 < r) (hχ : HasDerivAt χ χ' (Real.log r)) :
    HasDerivAt (fun t => χ (Real.log t / 2)) (χ' / (2 * r ^ 2)) (r ^ 2) := by
  have hc : HasDerivAt χ χ' (Real.log (r ^ 2) / 2) := by
    rw [log_sq_half]
    exact hχ
  have h := hc.comp (r ^ 2)
    ((Real.hasDerivAt_log (pow_ne_zero 2 hr.ne')).div_const 2)
  change HasDerivAt (fun t => χ (Real.log t / 2)) (χ' * ((r ^ 2)⁻¹ / 2)) (r ^ 2) at h
  convert h using 1
  field_simp

/-- A logarithmic radial cutoff has antiholomorphic norm `|χ'(log r)|/(2r)`. -/
theorem norm_dbarDifferential_logRadius {χ : ℝ → ℝ} {χ' : ℝ} {x : E}
    (hx : x ≠ 0) (hχ : HasDerivAt χ χ' (Real.log ‖x‖)) :
    ‖dbarDifferential (fun y : E => (χ (Real.log ‖y‖) : ℂ)) x‖ =
      |χ'| / (2 * ‖x‖) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := norm_dbarDifferential_radial_sq (hasDerivAt_logHalfProfile hr hχ)
  dsimp only at h
  simp_rw [log_sq_half] at h
  rw [h, abs_div, abs_of_pos (mul_pos two_pos (sq_pos_of_pos hr))]
  field_simp

/-- The holomorphic amplitude's degree is absent from the logarithmic cutoff derivative. -/
theorem norm_dbarDifferential_holomorphic_logRadius
    {h : E → ℂ} {χ : ℝ → ℝ} {χ' : ℝ} {x : E}
    (hx : x ≠ 0) (hh : DifferentiableAt ℂ h x)
    (hχ : HasDerivAt χ χ' (Real.log ‖x‖)) :
    ‖dbarDifferential (fun y : E => h y * (χ (Real.log ‖y‖) : ℂ)) x‖ =
      ‖h x‖ * (|χ'| / (2 * ‖x‖)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h := norm_dbarDifferential_holomorphic_radial_sq hh (hasDerivAt_logHalfProfile hr hχ)
  dsimp only at h
  simp_rw [log_sq_half] at h
  rw [h, abs_div, abs_of_pos (mul_pos two_pos (sq_pos_of_pos hr))]
  congr 1
  field_simp

end HTGeometry
