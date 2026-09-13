import GaloisForLFunctions.HTGeometry.InterfinityGeometry.HadamardDivision

/-!
# Smooth extension of a quotient by the coordinate

The quotient of a smooth real function vanishing at the origin has a canonical smooth extension:
average its derivative along the radial segment from zero to the evaluation point.  This packages
the removable-quotient identity in a form usable without repeatedly reproving a fundamental-theorem
of-calculus argument.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesHadamardQuotient

open Interfinity

noncomputable section

/-- Canonical extension of `h(s) / s` through `s = 0`. -/
def smoothCoordinateQuotient (h : ℝ → ℝ) : ℝ → ℝ :=
  hadamardAvg 0 (deriv h)

/-- Smoothness of the canonical quotient extension. -/
theorem smooth_smoothCoordinateQuotient {h : ℝ → ℝ} (hh : IsSmoothReal h) :
    IsSmoothReal (smoothCoordinateQuotient h) :=
  isSmoothReal_hadamardAvg 0 hh.derivSmooth

/-- Exact factorization of a function vanishing at the origin. -/
theorem mul_smoothCoordinateQuotient {h : ℝ → ℝ} (hh : IsSmoothReal h)
    (hzero : h 0 = 0) (s : ℝ) :
    s * smoothCoordinateQuotient h s = h s := by
  have hfactor := hadamard_eq hh s
  rw [hzero, zero_add] at hfactor
  exact hfactor.symm

/-- Away from zero, the canonical extension equals the literal quotient. -/
theorem smoothCoordinateQuotient_eq_div {h : ℝ → ℝ} (hh : IsSmoothReal h)
    (hzero : h 0 = 0) {s : ℝ} (hs : s ≠ 0) :
    smoothCoordinateQuotient h s = h s / s := by
  apply (mul_left_cancel₀ hs)
  rw [mul_smoothCoordinateQuotient hh hzero, mul_div_cancel₀ _ hs]

/-- Integral form of the removable quotient identity. -/
theorem div_eq_integral_deriv_scale {h : ℝ → ℝ} (hh : IsSmoothReal h)
    (hzero : h 0 = 0) {s : ℝ} (hs : s ≠ 0) :
    h s / s = ∫ t in (0 : ℝ)..1, deriv h (t * s) := by
  rw [← smoothCoordinateQuotient_eq_div hh hzero hs]
  simp only [smoothCoordinateQuotient, hadamardAvg, pow_zero, one_mul]

/-- The value filling the removable singularity is the derivative at the origin. -/
theorem smoothCoordinateQuotient_zero {h : ℝ → ℝ} :
    smoothCoordinateQuotient h 0 = deriv h 0 := by
  rw [smoothCoordinateQuotient, hadamardAvg]
  simp only [mul_zero, pow_zero, one_mul, intervalIntegral.integral_const, sub_zero, one_smul]

end

end GaloisForLFunctions.HTGeometry.NavierStokesHadamardQuotient
