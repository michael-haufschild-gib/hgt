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
      exact norm_nonneg _
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

end HTGeometry
