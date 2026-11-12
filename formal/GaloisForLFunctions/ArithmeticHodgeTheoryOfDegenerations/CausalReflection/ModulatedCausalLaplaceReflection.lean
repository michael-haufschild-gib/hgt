import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ModulatedCausalReflectionEnergy

/-!
# Complex Laplace zeros preserve causal-reflection support

The complex rate combines real exponential decay with modulation. Its
Laplace coefficient is exactly the real-rate coefficient of the modulated
input, so a zero removes the entire positive convolution tail.
-/

noncomputable section
open MeasureTheory Filter
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Physical complex decay rate in the Fourier normalization of the causal kernel. -/
def modulatedLaplaceRate (a b : ℝ) : ℂ :=
  ((Real.pi * a : ℝ) : ℂ) + ((2 * Real.pi * b : ℝ) : ℂ) * Complex.I

/-- Modulation converts the complex Laplace coefficient into the real-rate one. -/
theorem integral_modulated_laplace_eq (a b : ℝ) (f : ℝ → ℂ) :
    (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * causalModulation b f u) =
      negativeHalfLineLaplace f (modulatedLaplaceRate a b) := by
  unfold negativeHalfLineLaplace
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  change Complex.exp ((Real.pi * a * u : ℝ) : ℂ) *
      (Complex.exp (((2 * Real.pi * b * u : ℝ) : ℂ) * Complex.I) * f u) =
    Complex.exp (modulatedLaplaceRate a b * (u : ℂ)) * f u
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  unfold modulatedLaplaceRate
  push_cast
  ring

/-- A complex Laplace zero removes the positive tail of the actual modulated resolvent. -/
theorem modulatedCausalConvolution_support_of_laplace_zero (a b : ℝ) {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate a b) = 0) :
    ∀ u, 0 ≤ u → modulatedCausalConvolution a b f u = 0 := by
  have hm : ∀ u, 0 ≤ u → causalModulation b f u = 0 := by
    intro u hu
    rw [causalModulation, hf u hu, mul_zero]
  have hzm : (∫ u, Complex.exp ((Real.pi * a * u : ℝ) : ℂ) * causalModulation b f u) = 0 := by
    rw [integral_modulated_laplace_eq, hz]
  intro u hu
  rw [modulatedCausalConvolution_eq_conjugate, causalModulation,
    causalExponentialConvolution_support_of_laplace_zero a hm hzm u hu, mul_zero]

/-- A reflection at a complex Laplace zero retains negative-half-line support. -/
theorem modulatedCausalReflection_support_of_laplace_zero (a b : ℝ) {f : ℝ → ℂ}
    (hf : ∀ u, 0 ≤ u → f u = 0)
    (hz : negativeHalfLineLaplace f (modulatedLaplaceRate a b) = 0) :
    ∀ u, 0 ≤ u → modulatedCausalReflection a b f u = 0 := by
  intro u hu
  rw [modulatedCausalReflection, hf u hu,
    modulatedCausalConvolution_support_of_laplace_zero a b hf hz u hu,
    neg_zero, mul_zero, add_zero]

end GaloisForLFunctions.HTGeometry
