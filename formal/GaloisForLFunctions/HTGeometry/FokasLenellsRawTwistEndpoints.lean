import GaloisForLFunctions.HTGeometry.FokasLenellsRawTwistPrimitives

/-!
# Imaginary-ray covariance of both actual endpoint coefficient matrices

Absolute integrability permits transport of the complex-linear swap
through each endpoint integral. The resulting matrix identities retain
every endpoint correction needed for the fifth scattering coefficient.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawSecondEndpoint_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawSecondEndpoint (twistedPotential q) 0 (rawJetSwap v) left =
      -rawJetSwap (rawSecondEndpoint q 0 v left) := by
  have he : rawOrientedSecondIntegrand (twistedPotential q) 0 (rawJetSwap v) left =
      fun x => -rawJetSwap (rawOrientedSecondIntegrand q 0 v left x) := by
    funext x
    cases left <;> simp only [rawOrientedSecondIntegrand, Bool.false_eq_true, ↓reduceIte,
      rawSecondIntegrand_twisted_zero_swap, map_neg, neg_neg]
  simp only [rawSecondEndpoint, he]
  rw [integral_neg, rawJetSwap.integral_comp_comm (rawOrientedSecondIntegrand_integrable q 0 v left).integrableOn]

theorem rawThirdEndpoint_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawThirdEndpoint (twistedPotential q) 0 (rawJetSwap v) left =
      -I • rawJetSwap (rawThirdEndpoint q 0 v left) := by
  have he : rawOrientedThirdIntegrand (twistedPotential q) 0 (rawJetSwap v) left =
      fun x => -I • rawJetSwap (rawOrientedThirdIntegrand q 0 v left x) := by
    funext x
    cases left <;> simp only [rawOrientedThirdIntegrand, Bool.false_eq_true, ↓reduceIte,
      rawThirdIntegrand_twisted_zero_swap, map_neg, smul_neg]
  simp only [rawThirdEndpoint, he]
  rw [integral_smul, rawJetSwap.integral_comp_comm (rawOrientedThirdIntegrand_integrable q 0 v left).integrableOn]

theorem rawFourthEndpoint_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawFourthEndpoint (twistedPotential q) 0 (rawJetSwap v) left =
      rawJetSwap (rawFourthEndpoint q 0 v left) := by
  have he : rawOrientedFourthIntegrand (twistedPotential q) 0 (rawJetSwap v) left =
      fun x => rawJetSwap (rawOrientedFourthIntegrand q 0 v left x) := by
    funext x
    cases left <;> simp only [rawOrientedFourthIntegrand, Bool.false_eq_true, ↓reduceIte,
      rawFourthIntegrand_twisted_zero_swap, map_neg]
  simp only [rawFourthEndpoint, he]
  rw [rawJetSwap.integral_comp_comm (rawOrientedFourthIntegrand_integrable q 0 v left).integrableOn]

theorem rawFifthEndpoint_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (left : Bool) :
    rawFifthEndpoint (twistedPotential q) 0 (rawJetSwap v) left =
      I • rawJetSwap (rawFifthEndpoint q 0 v left) := by
  have he : rawOrientedFifthIntegrand (twistedPotential q) 0 (rawJetSwap v) left =
      fun x => I • rawJetSwap (rawOrientedFifthIntegrand q 0 v left x) := by
    funext x
    cases left <;> simp only [rawOrientedFifthIntegrand, Bool.false_eq_true, ↓reduceIte,
      rawFifthIntegrand_twisted_zero_swap, map_neg, smul_neg]
  simp only [rawFifthEndpoint, he]
  rw [integral_smul, rawJetSwap.integral_comp_comm (rawOrientedFifthIntegrand_integrable q 0 v left).integrableOn]

theorem rawFirstCoefficientMatrix_twisted (q : SchwartzMap ℝ ℂ) :
    rawFirstCoefficientMatrix (twistedPotential q) =
      I • (swapMatrix * rawFirstCoefficientMatrix q * swapMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawFirstCoefficientMatrix, swapMatrix, twistedPotential_apply, smul_eq_mul]

theorem rawQuadraticEndpointMatrix_twisted (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuadraticEndpointMatrix (twistedPotential q) left =
      -(swapMatrix * rawQuadraticEndpointMatrix q left * swapMatrix) := by
  have h0 : rawSecondEndpoint (twistedPotential q) 0 (1,0) left =
      -rawJetSwap (rawSecondEndpoint q 0 (0,1) left) := rawSecondEndpoint_twisted_zero_swap q (0,1) left
  have h1 : rawSecondEndpoint (twistedPotential q) 0 (0,1) left =
      -rawJetSwap (rawSecondEndpoint q 0 (1,0) left) := rawSecondEndpoint_twisted_zero_swap q (1,0) left
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawQuadraticEndpointMatrix, h0, h1, rawJetSwap_apply, swapMatrix]

theorem rawCubicEndpointMatrix_twisted_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawCubicEndpointMatrix (twistedPotential q) 0 left =
      -I • (swapMatrix * rawCubicEndpointMatrix q 0 left * swapMatrix) := by
  have h0 : rawThirdEndpoint (twistedPotential q) 0 (1,0) left =
      -I • rawJetSwap (rawThirdEndpoint q 0 (0,1) left) := rawThirdEndpoint_twisted_zero_swap q (0,1) left
  have h1 : rawThirdEndpoint (twistedPotential q) 0 (0,1) left =
      -I • rawJetSwap (rawThirdEndpoint q 0 (1,0) left) := rawThirdEndpoint_twisted_zero_swap q (1,0) left
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawCubicEndpointMatrix, h0, h1, rawJetSwap_apply, swapMatrix, smul_eq_mul]

theorem rawQuarticEndpointMatrix_twisted (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuarticEndpointMatrix (twistedPotential q) left =
      swapMatrix * rawQuarticEndpointMatrix q left * swapMatrix := by
  have h0 : rawFourthEndpoint (twistedPotential q) 0 (1,0) left =
      rawJetSwap (rawFourthEndpoint q 0 (0,1) left) := rawFourthEndpoint_twisted_zero_swap q (0,1) left
  have h1 : rawFourthEndpoint (twistedPotential q) 0 (0,1) left =
      rawJetSwap (rawFourthEndpoint q 0 (1,0) left) := rawFourthEndpoint_twisted_zero_swap q (1,0) left
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawQuarticEndpointMatrix, h0, h1, rawJetSwap_apply, swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem rawQuinticEndpointMatrix_twisted_zero (q : SchwartzMap ℝ ℂ) (left : Bool) :
    rawQuinticEndpointMatrix (twistedPotential q) 0 left =
      I • (swapMatrix * rawQuinticEndpointMatrix q 0 left * swapMatrix) := by
  have h0 : rawFifthEndpoint (twistedPotential q) 0 (1,0) left =
      I • rawJetSwap (rawFifthEndpoint q 0 (0,1) left) := rawFifthEndpoint_twisted_zero_swap q (0,1) left
  have h1 : rawFifthEndpoint (twistedPotential q) 0 (0,1) left =
      I • rawJetSwap (rawFifthEndpoint q 0 (1,0) left) := rawFifthEndpoint_twisted_zero_swap q (1,0) left
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawQuinticEndpointMatrix, h0, h1, rawJetSwap_apply, swapMatrix, smul_eq_mul]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
