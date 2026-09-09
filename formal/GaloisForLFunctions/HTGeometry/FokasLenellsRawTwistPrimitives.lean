import GaloisForLFunctions.HTGeometry.FokasLenellsRawTwistKernels

/-!
# Imaginary-ray covariance through the actual fifth primitive

The actual defining integrals transport the phases of the linear,
cubic and quintic kernels. All spatial coefficients through order five
therefore inherit the expected cyclic imaginary phases.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

theorem rawThirdIntegrand_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawThirdIntegrand (twistedPotential q) 0 (rawJetSwap v) x =
      -I • rawJetSwap (rawThirdIntegrand q 0 v x) := by
  simp only [rawThirdIntegrand, rawSecondSlope_twisted_zero_swap, rawInteractionSolution_zero_frequency,
    map_neg, rawDividedOperator_twisted_zero_swap, rawCubicOperator_twisted_zero_swap, map_add,
    smul_add, neg_smul]

theorem rawThirdSlope_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawThirdSlope (twistedPotential q) 0 (rawJetSwap v) x =
      -I • rawJetSwap (rawThirdSlope q 0 v x) := by
  simp only [rawThirdSlope]
  simp_rw [rawThirdIntegrand_twisted_zero_swap]
  rw [intervalIntegral.integral_smul,
    rawJetSwap.intervalIntegral_comp_comm (rawThirdIntegrand_integrable q 0 v).intervalIntegrable]

theorem rawFourthIntegrand_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawFourthIntegrand (twistedPotential q) 0 (rawJetSwap v) x =
      rawJetSwap (rawFourthIntegrand q 0 v x) := by
  simp only [rawFourthIntegrand, Complex.ofReal_zero, zero_smul, add_zero,
    rawThirdSlope_twisted_zero_swap, rawSolutionSlope_zero, rawLinearCoefficient_twisted_swap,
    map_smul, rawDividedOperator_twisted_zero_swap, rawCubicOperator_twisted_zero_swap, map_add,
    smul_smul, neg_mul, mul_neg, ← pow_two, I_sq, neg_neg, one_smul]

theorem rawFourthSlope_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawFourthSlope (twistedPotential q) 0 (rawJetSwap v) x =
      rawJetSwap (rawFourthSlope q 0 v x) := by
  simp only [rawFourthSlope]
  simp_rw [rawFourthIntegrand_twisted_zero_swap]
  rw [rawJetSwap.intervalIntegral_comp_comm (rawFourthIntegrand_integrable q 0 v).intervalIntegrable]

theorem rawFifthIntegrand_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawFifthIntegrand (twistedPotential q) 0 (rawJetSwap v) x =
      I • rawJetSwap (rawFifthIntegrand q 0 v x) := by
  simp only [rawFifthIntegrand, rawFourthSlope_twisted_zero_swap, rawSecondSlope_twisted_zero_swap,
    rawInteractionSolution_zero_frequency, map_neg, rawDividedOperator_twisted_zero_swap,
    rawCubicOperator_twisted_zero_swap, rawQuinticOperator_twisted_zero_swap, map_add, smul_add,
    neg_smul, neg_neg]

theorem rawFifthSlope_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawFifthSlope (twistedPotential q) 0 (rawJetSwap v) x =
      I • rawJetSwap (rawFifthSlope q 0 v x) := by
  simp only [rawFifthSlope]
  simp_rw [rawFifthIntegrand_twisted_zero_swap]
  rw [intervalIntegral.integral_smul,
    rawJetSwap.intervalIntegral_comp_comm (rawFifthIntegrand_integrable q 0 v).intervalIntegrable]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
