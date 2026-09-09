import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddFifthCovariance

/-!
# Imaginary-ray covariance of the actual zero-frequency kernels

The potential twist transports the complex-linear component swap with
the odd spectral phases I, -I, I. These are identities of the actual
constructed kernels, not a presumed formal power series.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Complex-linear component interchange for transporting spectral Taylor coefficients. -/
def rawJetSwap : RawOperator :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

@[simp] theorem rawJetSwap_apply (v : SpectralVector) : rawJetSwap v = (v.2,v.1) := rfl

@[simp] theorem rawJetSwap_involution (v : SpectralVector) : rawJetSwap (rawJetSwap v) = v := rfl

/-- The linear zero-frequency kernel gains one imaginary unit under the potential twist. -/
theorem rawDividedOperator_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    rawDividedOperator (twistedPotential q) 0 x (rawJetSwap v) =
      I • rawJetSwap (rawDividedOperator q 0 x v) := by
  apply Prod.ext <;>
    simp [rawDividedOperator_apply, rawJetSwap_apply, FDNLS.staggerPhase,
      SchwartzMap.derivCLM_apply, twistedPotential_deriv, twistedPotential_reflectedDerivative,
      smul_eq_mul, mul_assoc]

/-- The cubic zero-frequency kernel gains the opposite imaginary phase. -/
theorem rawCubicOperator_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    rawCubicOperator (twistedPotential q) 0 x (rawJetSwap v) =
      -I • rawJetSwap (rawCubicOperator q 0 x v) := by
  apply Prod.ext <;>
    simp [rawCubicOperator_zero_apply, rawJetSwap_apply, SchwartzMap.derivCLM_apply,
      twistedPotential_deriv, twistedPotential_reflectedDerivative, smul_eq_mul] <;> ring

/-- The quintic zero-frequency kernel returns to the positive imaginary phase. -/
theorem rawQuinticOperator_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (x : ℝ) (v : SpectralVector) :
    rawQuinticOperator (twistedPotential q) 0 x (rawJetSwap v) =
      I • rawJetSwap (rawQuinticOperator q 0 x v) := by
  apply Prod.ext <;>
    simp [rawQuinticOperator_zero_apply, rawJetSwap_apply,
      twistedPotential_deriv, twistedPotential_reflectedDerivative, smul_eq_mul, mul_assoc] <;> ring

/-- The actual anchored first primitive has precisely the same linear phase covariance. -/
theorem rawLinearCoefficient_twisted_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawLinearCoefficient (twistedPotential q) (rawJetSwap v) x =
      I • rawJetSwap (rawLinearCoefficient q v x) := by
  apply Prod.ext <;>
    simp [rawLinearCoefficient, rawLinearPrimitive, rawJetSwap_apply, twistedPotential_apply,
      smul_eq_mul, mul_assoc] <;> ring

/-- The true second-coefficient integrand acquires the squared imaginary phase. -/
theorem rawSecondIntegrand_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSecondIntegrand (twistedPotential q) 0 (rawJetSwap v) x =
      -rawJetSwap (rawSecondIntegrand q 0 v x) := by
  simp only [rawSecondIntegrand, Complex.ofReal_zero, zero_smul, add_zero, rawSolutionSlope_zero,
    rawLinearCoefficient_twisted_swap, map_smul, rawDividedOperator_twisted_zero_swap,
    smul_smul, ← pow_two, I_sq, neg_one_smul]

/-- Integration transports the same covariance to the actual second primitive. -/
theorem rawSecondSlope_twisted_zero_swap (q : SchwartzMap ℝ ℂ) (v : SpectralVector) (x : ℝ) :
    rawSecondSlope (twistedPotential q) 0 (rawJetSwap v) x =
      -rawJetSwap (rawSecondSlope q 0 v x) := by
  simp only [rawSecondSlope]
  simp_rw [rawSecondIntegrand_twisted_zero_swap]
  rw [intervalIntegral.integral_neg,
    rawJetSwap.intervalIntegral_comp_comm (rawSecondIntegrand_integrable q 0 v).intervalIntegrable]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
