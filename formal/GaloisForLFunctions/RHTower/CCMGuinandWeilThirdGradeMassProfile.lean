import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMatchedQuadrature
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCoordinateTransport
import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeRectangularMixture

/-!
# Literal CCM-FU triangular profile in polar mass coordinate

The outgoing matched-coverage seam is tested in the coordinate in which polar mass is Lebesgue.
This file establishes the exact differential geometry of the *literal* third-grade triangular
profile in that coordinate.  It is preparation for a nonlocal convex-hinge producer; no ordering
or boundedness of the arithmetic head is asserted here.
-/

open scoped BigOperators

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The literal third-grade triangular reporter pulled to outgoing polar mass coordinate. -/
def ccmThirdGradeCesaroPolarMassProfile (H y : ℝ) : ℝ :=
  ccmGuinandWeilThirdGradeCesaroTriangularWeight H
    (ccmActualHeadPolarHeightCoordinate y)

/-- First mass-coordinate derivative of the literal third-grade profile. -/
def ccmThirdGradeCesaroPolarMassProfileDeriv (H y : ℝ) : ℝ :=
  -(2 / y) * ccmGuinandWeilThirdGradeCesaroErrorKernel H
    (ccmActualHeadPolarHeightCoordinate y)

/-- Curvature of the literal triangular profile in polar mass coordinate. -/
def ccmThirdGradeCesaroPolarMassProfileCurvature (H y : ℝ) : ℝ :=
  (2 / y ^ 2) *
    (ccmGuinandWeilThirdGradeCesaroErrorKernel H
        (ccmActualHeadPolarHeightCoordinate y) +
      2 * ccmThirdGradeCesaroRectangularMixDensity H
        (ccmActualHeadPolarHeightCoordinate y))

private theorem hasDerivAt_ccmActualHeadPolarHeightCoordinate
    {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt ccmActualHeadPolarHeightCoordinate (2 / y) y := by
  unfold ccmActualHeadPolarHeightCoordinate
  have hdiv : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) y := by
    simpa only [id_eq, one_mul, mul_one] using (hasDerivAt_id y).div_const (2 : ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (x / 2)) (1 / y) y := by
    have hraw := (Real.hasDerivAt_log (div_ne_zero hy (by norm_num : (2 : ℝ) ≠ 0))).comp y hdiv
    change HasDerivAt (Real.log ∘ fun x : ℝ => x / 2) (1 / y) y
    exact hraw.congr_deriv (by field_simp [hy])
  exact (hlog.const_mul (2 : ℝ)).congr_deriv (by ring)

/-- **Mass-profile derivative law.** The literal moving triangular reporter has derivative equal
to the negative completed third-grade kernel times the polar-coordinate Jacobian `2/y`. -/
theorem hasDerivAt_ccmThirdGradeCesaroPolarMassProfile
    {H y : ℝ} (hy : y ≠ 0) (hh : ccmActualHeadPolarHeightCoordinate y ≠ 0) :
    HasDerivAt (ccmThirdGradeCesaroPolarMassProfile H)
      (ccmThirdGradeCesaroPolarMassProfileDeriv H y) y := by
  unfold ccmThirdGradeCesaroPolarMassProfile ccmThirdGradeCesaroPolarMassProfileDeriv
  have htri := hasDerivAt_ccmGuinandWeilThirdGradeCesaroTriangularWeight (H := H) hh
  have hheight := hasDerivAt_ccmActualHeadPolarHeightCoordinate hy
  rw [show (fun x : ℝ =>
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H
        (ccmActualHeadPolarHeightCoordinate x)) =
      ccmGuinandWeilThirdGradeCesaroTriangularWeight H ∘
        ccmActualHeadPolarHeightCoordinate by rfl]
  simpa only [Function.comp_apply] using (htri.comp y hheight).congr_deriv (by ring)

private theorem hasDerivAt_neg_two_div
    {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun x : ℝ => -(2 / x)) (2 / y ^ 2) y := by
  have hraw := (hasDerivAt_inv hy).const_mul (-2 : ℝ)
  have hfun : (fun x : ℝ => -(2 / x)) = fun x : ℝ => -2 * x⁻¹ := by
    funext x
    ring
  rw [hfun]
  exact hraw.congr_deriv (by field_simp [hy])

/-- **Strict mass-profile curvature law.** In polar mass coordinate, curvature is the completed
third-grade error kernel plus twice its positive rectangular-mixture density.  Thus the literal
triangular reporter has strictly positive local curvature throughout every physical window. -/
theorem hasDerivAt_ccmThirdGradeCesaroPolarMassProfileDeriv
    {H y : ℝ} (hH : H ≠ 0) (hy : y ≠ 0)
    (hh : ccmActualHeadPolarHeightCoordinate y ≠ 0) :
    HasDerivAt (ccmThirdGradeCesaroPolarMassProfileDeriv H)
      (ccmThirdGradeCesaroPolarMassProfileCurvature H y) y := by
  unfold ccmThirdGradeCesaroPolarMassProfileDeriv
    ccmThirdGradeCesaroPolarMassProfileCurvature
  have hfactor := hasDerivAt_neg_two_div hy
  have hkernel := hasDerivAt_ccmGuinandWeilThirdGradeCesaroErrorKernel hH hh
  have hheight := hasDerivAt_ccmActualHeadPolarHeightCoordinate hy
  have hcompose := hkernel.comp y hheight
  have hfun : (fun x : ℝ => -(2 / x) *
      ccmGuinandWeilThirdGradeCesaroErrorKernel H
        (ccmActualHeadPolarHeightCoordinate x)) =
      (fun x : ℝ => -(2 / x)) *
        (ccmGuinandWeilThirdGradeCesaroErrorKernel H ∘
          ccmActualHeadPolarHeightCoordinate) := by
    funext x
    simp only [Pi.mul_apply, Function.comp_apply]
  rw [hfun]
  exact (hfactor.mul hcompose).congr_deriv (by
    change 2 / y ^ 2 * ccmGuinandWeilThirdGradeCesaroErrorKernel H
        (ccmActualHeadPolarHeightCoordinate y) +
      (-(2 / y)) *
        (-ccmThirdGradeCesaroRectangularMixDensity H
          (ccmActualHeadPolarHeightCoordinate y) * (2 / y)) =
      (2 / y ^ 2) *
        (ccmGuinandWeilThirdGradeCesaroErrorKernel H
          (ccmActualHeadPolarHeightCoordinate y) +
          2 * ccmThirdGradeCesaroRectangularMixDensity H
            (ccmActualHeadPolarHeightCoordinate y))
    ring)

theorem ccmThirdGradeCesaroPolarMassProfileCurvature_pos
    {H y : ℝ} (hH : 0 < H) (hy : 0 < y)
    (hh : 0 < ccmActualHeadPolarHeightCoordinate y)
    (hhH : ccmActualHeadPolarHeightCoordinate y ≤ H) :
    0 < ccmThirdGradeCesaroPolarMassProfileCurvature H y := by
  unfold ccmThirdGradeCesaroPolarMassProfileCurvature
  have hkernel := ccmGuinandWeilThirdGradeCesaroErrorKernel_pos hh hhH ⟨le_rfl, hhH⟩
  have hdensity := ccmThirdGradeCesaroRectangularMixDensity_nonneg hH hh hhH
  have hsum : 0 < ccmGuinandWeilThirdGradeCesaroErrorKernel H
      (ccmActualHeadPolarHeightCoordinate y) +
        2 * ccmThirdGradeCesaroRectangularMixDensity H
          (ccmActualHeadPolarHeightCoordinate y) := by
    nlinarith
  exact mul_pos (by positivity) hsum

end GaloisForLFunctions.RHTower
