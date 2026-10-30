import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Vertical cancellation does not imply torus multiplicity

The auxiliary supported at `1`, `2`, and `3` has zero value and first derivative
along the logarithmic line through the identity, but a nonzero derivative in
the prime-two direction. Full-coordinate and vertical jet constraints must
therefore be distinguished. Coefficients here are real logarithms, not integers.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The three-term auxiliary supported at the integers `1`, `2`, and `3`. -/
def verticalFlatAuxiliary (z w : ℂ) : ℂ :=
  (Real.log 3 : ℂ) * (z - 1) - (Real.log 2 : ℂ) * (w - 1)

/-- Its restriction to the multiplicative logarithmic line. -/
def verticalFlatTrace (s : ℂ) : ℂ :=
  verticalFlatAuxiliary (Complex.exp (s * (Real.log 2 : ℂ)))
    (Complex.exp (s * (Real.log 3 : ℂ)))

theorem verticalFlatTrace_at_zero : verticalFlatTrace 0 = 0 := by
  simp only [verticalFlatTrace, verticalFlatAuxiliary, zero_mul, Complex.exp_zero,
    sub_self, mul_zero]

/-- The logarithmic-line derivative vanishes by exact cancellation of the two prime directions. -/
theorem verticalFlatTrace_derivative : HasDerivAt verticalFlatTrace 0 0 := by
  have h2 : HasDerivAt (fun s : ℂ => Complex.exp (s * (Real.log 2 : ℂ)))
      (Real.log 2 : ℂ) 0 := by
    simpa only [Function.comp_def, id_eq, zero_mul, Complex.exp_zero, one_mul] using
      (Complex.hasDerivAt_exp (0 * (Real.log 2 : ℂ))).comp 0
        ((hasDerivAt_id (0 : ℂ)).mul_const (Real.log 2 : ℂ))
  have h3 : HasDerivAt (fun s : ℂ => Complex.exp (s * (Real.log 3 : ℂ)))
      (Real.log 3 : ℂ) 0 := by
    simpa only [Function.comp_def, id_eq, zero_mul, Complex.exp_zero, one_mul] using
      (Complex.hasDerivAt_exp (0 * (Real.log 3 : ℂ))).comp 0
        ((hasDerivAt_id (0 : ℂ)).mul_const (Real.log 3 : ℂ))
  have h := ((h2.sub_const 1).const_mul (Real.log 3 : ℂ)).sub
    ((h3.sub_const 1).const_mul (Real.log 2 : ℂ))
  have hz : (Real.log 3 : ℂ) * (Real.log 2 : ℂ) -
      (Real.log 2 : ℂ) * (Real.log 3 : ℂ) = 0 := by ring
  rw [hz] at h
  exact h

/-- The same auxiliary has a nonzero first derivative in the prime-two coordinate. -/
theorem verticalFlatAuxiliary_transverse_jet :
    HasDerivAt (fun z : ℂ => verticalFlatAuxiliary z 1) (Real.log 3 : ℂ) 1 ∧
      (Real.log 3 : ℂ) ≠ 0 := by
  constructor
  · simpa only [id_eq, verticalFlatAuxiliary, sub_self, mul_zero, sub_zero, mul_one] using
      ((hasDerivAt_id (1 : ℂ)).sub_const 1).const_mul (Real.log 3 : ℂ)
  · exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 3)).ne'

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
