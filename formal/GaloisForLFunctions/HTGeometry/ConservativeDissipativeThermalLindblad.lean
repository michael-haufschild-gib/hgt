import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinLindblad

/-!
# Differential generator of the thermal conservative–dissipative channel

The precession and damping mechanism of arXiv:2609.04530 is realized here as a
two-jump Lindblad equation. Bath weights are constructed by normalized spin
coordinates. Actual differentiation of the analytic evolution identifies its
generator, and the nonnegative-time restriction is the previously verified
completely positive, trace-preserving thermal Kraus semigroup. These quantum
statements are corpus applications of the mechanism.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Two complementary jumps with constructed nonnegative bath weights and the original precession. -/
def spinThermalLindblad (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-Complex.I / 2) • (QuantumAlg.pauliZ * ρ - ρ * QuantumAlg.pauliZ) +
    ((2 * a ^ 2 * spinBathLower u : ℝ) : ℂ) • (spinLowering * ρ * spinLoweringᴴ -
      (1 / 2 : ℂ) • (spinLoweringᴴ * spinLowering * ρ + ρ * spinLoweringᴴ * spinLowering)) +
    ((2 * a ^ 2 * spinBathUpper u : ℝ) : ℂ) • (spinLoweringᴴ * ρ * spinLowering -
      (1 / 2 : ℂ) • (spinLowering * spinLoweringᴴ * ρ + ρ * spinLowering * spinLoweringᴴ))

set_option maxHeartbeats 600000 in
/-- Exact master-equation coordinates on all raw matrices. -/
theorem spinThermalLindblad_entries (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalLindblad a u ρ =
      !![((-2 * a ^ 2 : ℝ) : ℂ) * (ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ),
          spinPlaneRate a * ρ 0 1;
        conj (spinPlaneRate a) * ρ 1 0,
          ((-2 * a ^ 2 : ℝ) : ℂ) * (ρ 1 1 - (spinBathLower u : ℂ) * Matrix.trace ρ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinThermalLindblad, spinLowering, QuantumAlg.pauliZ, spinPlaneRate,
      spinBathLower, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- The thermal generator conserves trace without any input-state premise. -/
theorem spinThermalLindblad_trace (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (spinThermalLindblad a u ρ) = 0 := by
  rw [spinThermalLindblad_entries]
  simp [Matrix.trace, Fin.sum_univ_two, spinBathLower]
  ring

/-- The previously constructed bath is stationary in the differential equation itself. -/
theorem spinThermalLindblad_bath (a u : ℝ) : spinThermalLindblad a u (spinBathDensity u) = 0 := by
  rw [spinThermalLindblad_entries, spinBathDensity_trace, spinBathDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Thermal excitation is an exact trace-dependent correction to the existing downward generator. -/
theorem spinThermalLindblad_downward_split (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalLindblad a u ρ = spinLindblad a ρ +
      (((2 * a ^ 2 * spinBathUpper u : ℝ) : ℂ) * Matrix.trace ρ) • QuantumAlg.pauliZ := by
  rw [spinThermalLindblad_entries, spinLindblad_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QuantumAlg.pauliZ, Matrix.trace, Fin.sum_univ_two, spinBathLower] <;> ring

/-- Real analytic extension of the physical thermal semigroup. -/
def spinThermalEvolution (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.exp (-2 * a ^ 2 * t) : ℂ) * ρ 0 0 +
        (1 - (Real.exp (-2 * a ^ 2 * t) : ℂ)) * (spinBathUpper u : ℂ) * Matrix.trace ρ,
      spinPlaneFlow a 1 t * ρ 0 1;
    conj (spinPlaneFlow a 1 t) * ρ 1 0,
      (Real.exp (-2 * a ^ 2 * t) : ℂ) * ρ 1 1 +
        (1 - (Real.exp (-2 * a ^ 2 * t) : ℂ)) * (spinBathLower u : ℂ) * Matrix.trace ρ]

/-- Trace is conserved even on the full analytic extension. -/
theorem spinThermalEvolution_trace (a u t : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.trace (spinThermalEvolution a u ρ t) = Matrix.trace ρ := by
  simp [spinThermalEvolution, Matrix.trace, Fin.sum_univ_two, spinBathLower]
  ring

/-- Forward analytic evolution is the already proved completely positive, trace-preserving channel. -/
theorem spinThermalEvolution_channel (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    spinThermalEvolution a u ρ (t : ℝ) = (spinThermalChannel a u t).map ρ := by
  rw [spinThermalChannel_entries]
  simp only [spinThermalEvolution, spinPlaneFlow, mul_one, spinDecayFactor, spinDecayMass]

/-- The analytic evolution starts at every raw input matrix. -/
theorem spinThermalEvolution_zero (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : spinThermalEvolution a u ρ 0 = ρ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinThermalEvolution, spinPlaneFlow_zero]

/-- Actual differentiation identifies the thermal channel's two-jump Lindblad generator. -/
theorem hasDerivAt_spinThermalEvolution (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    HasDerivAt (spinThermalEvolution a u ρ) (spinThermalLindblad a u (spinThermalEvolution a u ρ t)) t := by
  have hm := (((hasDerivAt_id t).const_mul (-2 * a ^ 2)).exp).ofReal_comp
  have hz := hasDerivAt_spinPlaneFlow a 1 t
  have hw := (hasDerivAt_const t (1 : ℂ)).sub hm
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · change HasDerivAt (fun v => (Real.exp (-2 * a ^ 2 * v) : ℂ) * ρ 0 0 +
      (1 - (Real.exp (-2 * a ^ 2 * v) : ℂ)) * (spinBathUpper u : ℂ) * Matrix.trace ρ) _ t
    apply ((hm.mul_const (ρ 0 0)).add ((hw.mul_const (spinBathUpper u : ℂ)).mul_const (Matrix.trace ρ))).congr_deriv
    rw [spinThermalLindblad_entries, spinThermalEvolution_trace]
    simp [spinThermalEvolution]
    ring
  · change HasDerivAt (fun v => spinPlaneFlow a 1 v * ρ 0 1) _ t
    apply (hz.mul_const (ρ 0 1)).congr_deriv
    simp [spinThermalLindblad_entries, spinThermalEvolution]
    ring
  · change HasDerivAt (fun v => conj (spinPlaneFlow a 1 v) * ρ 1 0) _ t
    apply (hz.star.mul_const (ρ 1 0)).congr_deriv
    simp [spinThermalLindblad_entries, spinThermalEvolution]
    ring
  · change HasDerivAt (fun v => (Real.exp (-2 * a ^ 2 * v) : ℂ) * ρ 1 1 +
      (1 - (Real.exp (-2 * a ^ 2 * v) : ℂ)) * (spinBathLower u : ℂ) * Matrix.trace ρ) _ t
    apply ((hm.mul_const (ρ 1 1)).add ((hw.mul_const (spinBathLower u : ℂ)).mul_const (Matrix.trace ρ))).congr_deriv
    rw [spinThermalLindblad_entries, spinThermalEvolution_trace]
    simp [spinThermalEvolution]
    ring

end
end GaloisForLFunctions.HTGeometry.SchafferExl
