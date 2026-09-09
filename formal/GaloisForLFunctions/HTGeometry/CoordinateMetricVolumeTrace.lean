import GaloisForLFunctions.HTGeometry.CoordinateMetricPathDensity
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.MetricPathDensity
noncomputable section
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

private theorem det_one_add_smul_hasDerivAt (B : Mat) :
    HasDerivAt (fun t : ℂ => (1 + t • B).det) B.trace 0 := by
  let P : Polynomial ℂ := Matrix.det
    ((1 : Matrix (Fin d) (Fin d) (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
      B.map (Polynomial.C : ℂ →+* Polynomial ℂ))
  have hp : HasDerivAt (fun t : ℂ => P.eval t) B.trace 0 := by
    convert! P.hasDerivAt 0 using 1
    simpa [P] using! (Matrix.derivative_det_one_add_X_smul B).symm
  convert! hp using 1
  funext t
  simp [P, eval_det, ← Matrix.smul_eq_mul_diagonal]

/-- The actual complex determinant slope equals the full inverse-trace contraction. -/
theorem determinantSlope_eq_det_mul_trace (G H : Mat) (hG : G.det ≠ 0) :
    determinantSlope G H = G.det * (G⁻¹ * H).trace := by
  have hl := determinant_hasDerivAt G H 0 0
  have hr := (det_one_add_smul_hasDerivAt (G⁻¹ * H)).const_mul G.det
  apply hl.unique
  convert! hr using 1
  funext t
  calc
    (path G H 0 0 t).det = (G * (1 + t • (G⁻¹ * H))).det := by
      congr 1
      simp only [path, smul_zero, add_zero, Matrix.mul_add, Matrix.mul_one,
        Matrix.mul_smul, Matrix.mul_nonsing_inv_cancel_left G H (isUnit_iff_ne_zero.mpr hG)]
    _ = _ := Matrix.det_mul _ _

/-- The fixed local volume branch has the standard half-trace derivative, derived from its determinant. -/
theorem volumeRatio_hasDerivAt_trace (G H K L : Mat) (hG : G.det ≠ 0) :
    HasDerivAt (volumeRatio G H K L) ((G⁻¹ * H).trace / 2) 0 := by
  convert! volumeRatio_hasDerivAt G H K L hG using 1
  rw [determinantSlope_eq_det_mul_trace G H hG]
  field_simp

end
end GaloisForLFunctions.HTGeometry.MetricPathDensity
