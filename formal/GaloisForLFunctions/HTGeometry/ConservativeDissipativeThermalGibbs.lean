import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalAmplitude
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinPinching

/-!
# Thermal quantum realization of the Schaffer–Exl dissipative mechanism

The conservative–dissipative split of arXiv:2609.04530 motivates the explicit
thermal amplitude semigroup constructed in `ConservativeDissipativeThermalAmplitude`.
Here its stationary carrier is identified with the existing zero-coupling Gibbs
density. Positive rates are constructed exponentially; all raw input matrices
converge to their conserved trace times that bath. These quantum consequences
are corpus applications, not claims that the paper proves quantum thermalization.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Exponentially parametrized bath coordinates recover the exact Gibbs upper population. -/
theorem spinBathUpper_gibbs (b : ℝ) : spinBathUpper (Real.exp (-b)) = (1 + Real.tanh b) / 2 := by
  have hp : Real.exp (-b) ^ 2 = Real.exp (2 * (-b)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h := spinLatitude_exp_tanh (-b)
  rw [Real.tanh_neg] at h
  unfold spinBathUpper spinMixRadius
  rw [hp]
  have hd : 1 + Real.exp (2 * (-b)) ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith

/-- Exact Gibbs lower population in the same unrestricted bias coordinate. -/
theorem spinBathLower_gibbs (b : ℝ) : spinBathLower (Real.exp (-b)) = (1 - Real.tanh b) / 2 := by
  rw [spinBathLower, spinBathUpper_gibbs]
  ring

/-- The constructed stationary bath is the corpus's literal zero-coupling Gibbs density. -/
theorem spinBathDensity_gibbs (b : ℝ) : spinBathDensity (Real.exp (-b)) = qubitDensity 0 b := by
  rw [spinBathDensity_entries, spinBathUpper_gibbs, spinBathLower_gibbs, qubitDensity_zero_coupling]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [QuantumAlg.pauliZ, Matrix.smul_apply] <;> ring

/-- Every existing Gibbs state in the zero-coupling family is fixed by a constructed physical semigroup. -/
theorem spinThermalChannel_gibbs_fixed (a b : ℝ) (t : NNReal) :
    (spinThermalChannel a (Real.exp (-b)) t).map (qubitDensity 0 b) = qubitDensity 0 b := by
  rw [← spinBathDensity_gibbs, spinThermalChannel_bath_fixed]

/-- Coherence decays on the full nonnegative continuous-time domain under constructed positive damping. -/
theorem spinDecayFactor_tendsto_zero (s : ℝ) :
    Tendsto (spinDecayFactor (Real.exp s)) atTop (nhds 0) := by
  have hc : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have h := (spinPlaneFlow_positive_tendsto_zero s 1).comp hc
  unfold spinPlaneFlow at h
  change Tendsto (fun t : NNReal => Complex.exp (spinPlaneRate (Real.exp s) * ((t : ℝ) : ℂ))) atTop (nhds 0)
  simpa only [Function.comp_def, mul_one] using h

/-- The surviving population has zero limit on that same time domain. -/
theorem spinDecayMass_tendsto_zero (s : ℝ) :
    Tendsto (spinDecayMass (Real.exp s)) atTop (nhds 0) := by
  have h := (spinDecayFactor_tendsto_zero s).norm.pow 2
  simpa only [spinDecayFactor_norm_sq, norm_zero, zero_pow two_ne_zero] using h

/-- Every raw input matrix converges to its conserved trace times the exact bath density. -/
theorem spinThermalChannel_tendsto_trace_bath (s u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t : NNReal => (spinThermalChannel (Real.exp s) u t).map ρ)
      atTop (nhds ((Matrix.trace ρ) • spinBathDensity u)) := by
  have hm := (spinDecayMass_tendsto_zero s).ofReal
  have hz := spinDecayFactor_tendsto_zero s
  have h00 := (hm.mul_const (ρ 0 0)).add
    ((((tendsto_const_nhds (x := (1 : ℂ))).sub hm).mul_const (spinBathUpper u : ℂ)).mul_const (Matrix.trace ρ))
  have h11 := (hm.mul_const (ρ 1 1)).add
    ((((tendsto_const_nhds (x := (1 : ℂ))).sub hm).mul_const (spinBathLower u : ℂ)).mul_const (Matrix.trace ρ))
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [spinThermalChannel_entries, spinBathDensity_entries, Matrix.smul_apply, mul_comm] using h00
  · simpa [spinThermalChannel_entries, spinBathDensity_entries, Matrix.smul_apply] using hz.mul_const (ρ 0 1)
  · simpa [spinThermalChannel_entries, spinBathDensity_entries, Matrix.smul_apply] using hz.star.mul_const (ρ 1 0)
  · simpa [spinThermalChannel_entries, spinBathDensity_entries, Matrix.smul_apply, mul_comm] using h11

/-- Constructed normalized pure inputs converge to the actual stationary bath with no normalization premise. -/
theorem spinThermalChannel_pure_tendsto_bath (s u : ℝ) (z : ℂ) :
    Tendsto (fun t : NNReal => (spinThermalChannel (Real.exp s) u t).map (spinChartDensity z))
      atTop (nhds (spinBathDensity u)) := by
  simpa only [spinChartDensity_trace, one_smul] using
    spinThermalChannel_tendsto_trace_bath s u (spinChartDensity z)

/-- Physical thermal relaxation ends in the existing literal Gibbs carrier. -/
theorem spinThermalChannel_pure_tendsto_gibbs (s b : ℝ) (z : ℂ) :
    Tendsto (fun t : NNReal => (spinThermalChannel (Real.exp s) (Real.exp (-b)) t).map (spinChartDensity z))
      atTop (nhds (qubitDensity 0 b)) := by
  rw [← spinBathDensity_gibbs]
  exact spinThermalChannel_pure_tendsto_bath s _ z

end
end GaloisForLFunctions.HTGeometry.SchafferExl
