import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ComplexCausalLaplaceDuality

/-!
# Complex moments from the anti-causal representation

At a Laplace zero, the growing weighted causal kernel can be replaced by
a decaying reflected kernel. Both representations give the same exact
resolvent coefficient on their respective open half-planes.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry

/-- A reflected exponential kernel shifts its rate in the opposite direction. -/
theorem complexLaplaceWeighted_reflectedKernel (q z : ℂ) :
    complexLaplaceWeighted q (fun u => complexRateCausalKernel z (-u)) =
      fun u => complexRateCausalKernel (z + q) (-u) := by
  funext u
  have h := congrFun (complexLaplaceWeighted_causalKernel (-q) z) (-u)
  simpa only [complexLaplaceWeighted, Complex.ofReal_neg, neg_mul_neg,
    sub_neg_eq_add] using h

/-- Reflection preserves the total complex kernel mass. -/
theorem integral_reflectedComplexCausalKernel {z : ℂ} (hz : 0 < z.re) :
    (∫ u, complexRateCausalKernel z (-u)) = (Real.pi : ℂ) / z := by
  calc
    _ = ∫ u, complexRateCausalKernel z u := by
      simpa only [zero_sub] using
        integral_sub_left_eq_self (μ := volume) (complexRateCausalKernel z) 0
    _ = _ := integral_complexRateCausalKernel hz

/-- Beyond the causal decay range, the reflected kernel gives the same moment law. -/
theorem negativeHalfLineLaplace_causalConvolution_of_gt {z q : ℂ}
    (hdecay : 0 < (q - z).re) {f : ℝ → ℂ}
    (hi : Integrable (complexLaplaceWeighted z f))
    (hz : negativeHalfLineLaplace f z = 0)
    (hf : Integrable (complexLaplaceWeighted q f)) :
    negativeHalfLineLaplace (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) q =
      ((Real.pi : ℂ) / (z - q)) * negativeHalfLineLaplace f q := by
  have hfun : complexLaplaceWeighted q
      (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      fun y => -(((fun t => complexRateCausalKernel (q - z) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        complexLaplaceWeighted q f) y) := by
    rw [complexCausalConvolution_eq_neg_reflected_of_laplace_zero hi hz]
    calc
      _ = fun y => -complexLaplaceWeighted q
          ((fun t => complexRateCausalKernel (-z) (-t)) ⋆[ContinuousLinearMap.mul ℂ ℂ] f) y := by
        funext y
        exact mul_neg _ _
      _ = _ := by
        rw [complexLaplaceWeighted_convolution, complexLaplaceWeighted_reflectedKernel,
          show -z + q = q - z by ring]
  change (∫ u, complexLaplaceWeighted q
    (complexRateCausalKernel z ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u) = _
  rw [hfun, integral_neg,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (integrable_complexRateCausalKernel hdecay).comp_neg hf,
    integral_reflectedComplexCausalKernel hdecay]
  change -(((Real.pi : ℂ) / (q - z)) * negativeHalfLineLaplace f q) = _
  rw [show q - z = -(z - q) by ring, div_neg, neg_mul, neg_neg]

end GaloisForLFunctions.HTGeometry
