import GaloisForLFunctions.HTGeometry.UpperHalfPlaneFiniteBlaschkeCayley

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exact pseudohyperbolic separation of a horizontal crossing pair. -/
theorem norm_upperHalfPlaneBlaschkeFactor_horizontalPair
    {a omega gamma : ℝ} (ha : 0 < a) (homega : 0 ≤ omega) :
    ‖upperHalfPlaneBlaschkeFactor
        ((-gamma : ℂ) + ((a + omega : ℝ) : ℂ) * I)
        ((-gamma : ℂ) + ((a - omega : ℝ) : ℂ) * I)‖ =
      omega / a := by
  have hnum :
      ((-gamma : ℂ) + ((a - omega : ℝ) : ℂ) * I) -
          ((-gamma : ℂ) + ((a + omega : ℝ) : ℂ) * I) =
        ((-2 * omega : ℝ) : ℂ) * I := by
    push_cast
    ring
  have hden :
      ((-gamma : ℂ) + ((a - omega : ℝ) : ℂ) * I) -
          (starRingEnd ℂ)
            ((-gamma : ℂ) + ((a + omega : ℝ) : ℂ) * I) =
        ((2 * a : ℝ) : ℂ) * I := by
    simp only [map_add, map_neg, conj_ofReal, map_mul, conj_I]
    push_cast
    ring
  rw [upperHalfPlaneBlaschkeFactor, norm_div, hnum, hden,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, norm_I, mul_one,
    abs_of_nonpos (by linarith), abs_of_pos (by linarith)]
  field_simp

/-- Along the ray `omega = lambda * a`, one crossing Blaschke factor has exact modulus `lambda`. -/
theorem norm_upperHalfPlaneBlaschkeFactor_horizontalRay
    {a lambda gamma : ℝ} (ha : 0 < a) (hlambda0 : 0 ≤ lambda) :
    ‖upperHalfPlaneBlaschkeFactor
        ((-gamma : ℂ) + (((1 + lambda) * a : ℝ) : ℂ) * I)
        ((-gamma : ℂ) + (((1 - lambda) * a : ℝ) : ℂ) * I)‖ =
      lambda := by
  have h := norm_upperHalfPlaneBlaschkeFactor_horizontalPair
    (a := a) (omega := lambda * a) (gamma := gamma) ha
    (mul_nonneg hlambda0 ha.le)
  convert h using 1
  · congr 4 <;> push_cast <;> ring
  · field_simp

/-- A crossing zero of multiplicity `m` contributes the exact local modulus `lambda ^ m`. -/
theorem norm_pow_upperHalfPlaneBlaschkeFactor_horizontalRay
    {a lambda gamma : ℝ} (m : ℕ) (ha : 0 < a) (hlambda0 : 0 ≤ lambda) :
    ‖upperHalfPlaneBlaschkeFactor
        ((-gamma : ℂ) + (((1 + lambda) * a : ℝ) : ℂ) * I)
        ((-gamma : ℂ) + (((1 - lambda) * a : ℝ) : ℂ) * I) ^ m‖ =
      lambda ^ m := by
  rw [norm_pow,
    norm_upperHalfPlaneBlaschkeFactor_horizontalRay ha hlambda0]

end

end GaloisForLFunctions.HTGeometry
