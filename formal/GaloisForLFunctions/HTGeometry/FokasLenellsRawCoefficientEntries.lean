import GaloisForLFunctions.HTGeometry.FokasLenellsRawCoefficientEndpoints

/-!
# Explicit entries of the genuine low-frequency scattering coefficients

The quadratic coefficient is diagonal. The cubic reflection coefficient is
reduced to one whole-line integral of the actual third integrand plus the
explicit anchoring correction. This isolates the expression to be compared
with the paper's compatibility moment.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- The actual quadratic scattering coefficient is a single mixed moment with opposite diagonal signs. -/
theorem rawScatteringQuadraticCoefficient_eq (q : SchwartzMap ℝ ℂ) :
    rawScatteringQuadraticCoefficient q = !![-rawMixedTotal q,0;0,rawMixedTotal q] := by
  have hJ := rawMixedEndpoint_difference q
  have hR : rawMixedEndpoint q false = rawMixedEndpoint q true+rawMixedTotal q := by
    linear_combination hJ
  unfold rawScatteringQuadraticCoefficient
  simp only [rawQuadraticEndpointMatrix_eq,hR]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawFirstCoefficientMatrix,Matrix.adjugate_fin_two] <;>
    ring_nf <;> simp only [I_sq] <;> ring

theorem rawScatteringQuadraticCoefficient_lower (q : SchwartzMap ℝ ℂ) :
    rawScatteringQuadraticCoefficient q 1 0 = 0 := by rw [rawScatteringQuadraticCoefficient_eq]; rfl

theorem rawScatteringQuadraticCoefficient_upper (q : SchwartzMap ℝ ℂ) :
    rawScatteringQuadraticCoefficient q 0 1 = 0 := by rw [rawScatteringQuadraticCoefficient_eq]; rfl

/-- The actual third integrand contains precisely the nested primitive and the spatial first moment. -/
theorem rawThirdIntegrand_zero_lower (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawThirdIntegrand q 0 (1,0) x).2 =
      -I*deriv q x*rawMixedPrimitive q x+I*q 0*deriv q x*q (-x)-
        I*(q 0)^(2 : ℕ)*deriv q x-2*(x : ℂ)*deriv q x := by
  unfold rawThirdIntegrand
  rw [rawSecondSlope_zero_eq,rawInteractionSolution_zero_frequency]
  simp only [rawDividedOperator_apply,rawCubicOperator_zero_apply,rawSecondPrimitive,
    Prod.snd_add,zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,FDNLS.staggerPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,SchwartzMap.derivCLM_apply]
  ring

/-- Combining the actual oriented cubic endpoints gives a full-line Bochner integral. -/
theorem rawThirdEndpoint_difference (q : SchwartzMap ℝ ℂ) (k : ℝ) (v : SpectralVector) :
    rawThirdEndpoint q k v false-rawThirdEndpoint q k v true = ∫ x : ℝ, rawThirdIntegrand q k v x := by
  have hh := intervalIntegral.integral_Iic_add_Ioi (μ := volume) (b := (0 : ℝ))
    (rawThirdIntegrand_integrable q k v).integrableOn (rawThirdIntegrand_integrable q k v).integrableOn
  unfold rawThirdEndpoint rawOrientedThirdIntegrand
  simp only [Bool.false_eq_true,↓reduceIte,integral_neg,integral_comp_neg_Ioi,neg_zero,sub_neg_eq_add]
  simpa only [add_comm] using hh

/-- Exact lower-left cubic coefficient of the actual scattering matrix, before local moment reduction. -/
theorem rawScatteringCubicCoefficient_lower_integral (q : SchwartzMap ℝ ℂ) :
    rawScatteringCubicCoefficient q 1 0 =
      (∫ x : ℝ, (rawThirdIntegrand q 0 (1,0) x).2)+I*q 0*rawMixedTotal q := by
  have hT := congrArg Prod.snd (rawThirdEndpoint_difference q 0 (1,0))
  simp only [Prod.snd_sub,snd_integral (rawThirdIntegrand_integrable q 0 (1,0))] at hT
  have hJ := rawMixedEndpoint_difference q
  simp only [rawScatteringCubicCoefficient,rawQuadraticEndpointMatrix_eq]
  simp [rawCubicEndpointMatrix,rawFirstCoefficientMatrix,Matrix.adjugate_fin_two]
  linear_combination hT+(I*q 0)*hJ

end
end GaloisForLFunctions.HTGeometry.FokasLenells
