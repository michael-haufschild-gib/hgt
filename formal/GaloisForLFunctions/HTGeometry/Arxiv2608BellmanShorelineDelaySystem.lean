import Mathlib

/-!
# Regular delay-system calculus from arXiv:2608.29060

This module supplies dimension-independent normalized-vector differentiation and isolates the exact
scalar denominator appearing in the paper's regular three-dimensional old-contact equations. It
then solves the implicit delay equation under precisely the paper's chamber nondegeneracy
condition. No switch-stratum or full-rank assumption is hidden in these local identities.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Remove component of `x` parallel to `n`. For unit `n`, this is `(I - nnᵀ)x`. -/
def bellmanShorelineOrthogonalProjection (n x : F) : F :=
  x - (inner ℝ n x) • n

/-- Derivative of normalized nonzero vector is projected velocity divided by original norm. -/
theorem bellmanShoreline_hasDerivAt_normalize
    {N : ℝ → F} {N' : F} {sigma : ℝ}
    (hN : HasDerivAt N N' sigma) (hne : N sigma ≠ 0) :
    HasDerivAt (fun s => ‖N s‖⁻¹ • N s)
      (‖N sigma‖⁻¹ • bellmanShorelineOrthogonalProjection
        (‖N sigma‖⁻¹ • N sigma) N') sigma := by
  have hnorm : HasDerivAt (fun s => ‖N s‖)
      (inner ℝ (N sigma) N' / ‖N sigma‖) sigma := by
    have hsqrt := hN.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))
    convert hsqrt using 1
    · funext s
      exact (Real.sqrt_sq (norm_nonneg (N s))).symm
    · rw [Real.sqrt_sq (norm_nonneg (N sigma))]
      field_simp [norm_ne_zero_iff.mpr hne]
  have hinv := hnorm.inv (norm_ne_zero_iff.mpr hne)
  have hproduct := hinv.smul hN
  convert hproduct using 1
  · rfl
  · simp only [Pi.inv_apply, bellmanShorelineOrthogonalProjection, smul_sub,
      real_inner_smul_left, smul_smul]
    field_simp [norm_ne_zero_iff.mpr hne]
    module

/-- Scalar old-contact denominator in regular three-dimensional delay chamber. -/
def bellmanShorelineDelayDenominator
    (kappa mu tau geodesicCurvature : ℝ) (n q : F) : ℝ :=
  -(1 + kappa ^ (2 : ℕ)) * mu * Real.exp (kappa * tau) +
    geodesicCurvature * inner ℝ n q

/-- Frenet contact identities reduce differentiated tangency factor to delay denominator. -/
theorem bellmanShoreline_delayDenominator_eq
    (kappa mu tau geodesicCurvature : ℝ) (n omega tangent q : F)
    (homega : inner ℝ n omega = mu * Real.exp (kappa * tau))
    (htangent : inner ℝ n tangent = -kappa * mu * Real.exp (kappa * tau)) :
    inner ℝ n (-omega + kappa • tangent + geodesicCurvature • q) =
      bellmanShorelineDelayDenominator kappa mu tau geodesicCurvature n q := by
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right,
    homega, htangent, bellmanShorelineDelayDenominator]
  ring

/-- Nonzero chamber denominator uniquely determines old-contact delay derivative. -/
theorem bellmanShoreline_regularDelayDerivative
    (kappa mu tau geodesicCurvature tauPrime normalVelocity : ℝ)
    (n q : F)
    (hden : bellmanShorelineDelayDenominator
      kappa mu tau geodesicCurvature n q ≠ 0)
    (hdiff : 0 = normalVelocity + (1 - tauPrime) *
      bellmanShorelineDelayDenominator kappa mu tau geodesicCurvature n q) :
    1 - tauPrime = -normalVelocity /
      bellmanShorelineDelayDenominator kappa mu tau geodesicCurvature n q := by
  field_simp [hden]
  linarith

end GaloisForLFunctions.HTGeometry

end
