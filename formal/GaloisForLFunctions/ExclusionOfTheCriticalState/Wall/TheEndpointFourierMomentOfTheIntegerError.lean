import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ParsevalForTheIntegerQuadrature

/-!
# The boundary line of the integer quadrature

At the half tilt the physical positive-ray square mass would dominate the
Fourier integrals on every approaching subcritical line. Fatou then bounds
the product of the boundary zeta values with the half-tilted state.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- On opposite rays the zero and half tilts dominate all intermediate
tilts at once, with an integrable majorant when the endpoint is finite. -/
theorem squared_intermediate_tilt_le {D : ℝ → ℝ} {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1/2) (t : ℝ) :
    (Real.exp (β*t)*D t)^2 ≤ (D t)^2 + (Ioi (0:ℝ)).indicator (fun v => (Real.exp (v/2)*D v)^2) t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from not_lt.mpr ht),add_zero,mul_pow]
    have h1 : Real.exp (β*t) ≤ 1 := Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hβ ht)
    exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (Real.exp_pos _).le h1)
  · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht),mul_pow,mul_pow]
    have h1 : Real.exp (β*t) ≤ Real.exp (t/2) := Real.exp_le_exp.2 (by
      linarith only [mul_le_mul_of_nonneg_right hβ' ht.le])
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) (sq_nonneg _)).trans
      (le_add_of_nonneg_left (sq_nonneg _))

end GaloisForLFunctions.ExclusionOfTheCriticalState
