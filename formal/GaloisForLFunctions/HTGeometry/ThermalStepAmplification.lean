import GaloisForLFunctions.HTGeometry.ChargedStepScattering
import GaloisForLFunctions.HTGeometry.ChargedStringThermalOccupation

/-!
# Thermal calibration of an actual amplifying charged interface

The horizon charge--temperature identity in arXiv:2608.21406 calibrates the
explicit C¹ step solution from `ChargedStepScattering`. Its step height equals
charge times the corpus black-hole horizon potential. Reflection is exactly
inverse normalized temperature and one plus the actual infinite thermal mean.
This coefficient belongs to this calibrated interface, not to every smooth
black-hole geometry. All parameters are unrestricted real data.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Charge times the nonvacuum horizon potential. -/
def thermalStepScale (e tau : ℝ) : ℝ := Real.exp e * coherentRadius tau

def thermalStepA (e tau : ℝ) : ℝ :=
  Real.log (thermalStepScale e tau * (1 - thermalRatio tau))

def thermalStepB (e tau : ℝ) : ℝ :=
  Real.log (thermalStepScale e tau * thermalRatio tau / 2)

def thermalStepFrequency (e tau : ℝ) : ℝ :=
  chargedStepMomentum (thermalStepA e tau) (thermalStepB e tau)

def thermalStepReflection (e tau : ℝ) : ℝ :=
  chargedStepReflection (thermalStepA e tau) (thermalStepB e tau)

def thermalStepTransmission (e tau : ℝ) : ℝ :=
  chargedStepTransmission (thermalStepA e tau) (thermalStepB e tau)

def thermalStepWave (e tau : ℝ) : ℝ → ℂ :=
  chargedStepWave (thermalStepA e tau) (thermalStepB e tau)

theorem thermalStepScale_pos (e tau : ℝ) : 0 < thermalStepScale e tau :=
  mul_pos (Real.exp_pos e) (coherentRadius_pos tau)

theorem thermalStepA_exp (e tau : ℝ) :
    Real.exp (thermalStepA e tau) = thermalStepScale e tau * (1 - thermalRatio tau) := by
  exact Real.exp_log (mul_pos (thermalStepScale_pos e tau) (sub_pos.mpr (thermalRatio_lt_one tau)))

theorem thermalStepB_exp (e tau : ℝ) :
    Real.exp (thermalStepB e tau) = thermalStepScale e tau * thermalRatio tau / 2 := by
  exact Real.exp_log (div_pos (mul_pos (thermalStepScale_pos e tau) (thermalRatio_pos tau)) (by norm_num))

theorem thermalStepFrequency_formula (e tau : ℝ) :
    thermalStepFrequency e tau = thermalStepScale e tau * (1 - thermalRatio tau / 2) := by
  rw [thermalStepFrequency, chargedStepMomentum, thermalStepA_exp, thermalStepB_exp]
  ring

/-- The chosen scattering frequency lies strictly in the upper half of the superradiant window. -/
theorem thermalStepFrequency_window (e tau : ℝ) :
    thermalStepScale e tau / 2 < thermalStepFrequency e tau ∧
      thermalStepFrequency e tau < thermalStepScale e tau := by
  rw [thermalStepFrequency_formula]
  have hs := thermalStepScale_pos e tau
  have hr := thermalRatio_pos tau
  have hr1 := thermalRatio_lt_one tau
  constructor <;> nlinarith

theorem thermalStepFrequency_pos (e tau : ℝ) : 0 < thermalStepFrequency e tau :=
  chargedStepMomentum_pos _ _

/-- The explicit step height is precisely charge times the actual horizon potential. -/
theorem thermalStep_horizon_height (e ell tau : ℝ) :
    chargedStepChemicalPotential (thermalStepA e tau) (thermalStepB e tau) 0 =
      Real.exp e * stringBlackHolePotential ell tau 0 := by
  simp only [chargedStepChemicalPotential, le_refl, if_true, thermalStepA_exp, thermalStepB_exp,
    stringBlackHolePotential, mul_zero, Real.exp_zero, mul_one]
  unfold thermalStepScale
  ring

theorem thermalStep_horizon_frequency (e ell tau : ℝ) :
    thermalStepFrequency e tau - Real.exp e * stringBlackHolePotential ell tau 0 =
      -thermalStepScale e tau * thermalRatio tau / 2 := by
  rw [← thermalStep_horizon_height e ell tau, thermalStepFrequency]
  simp only [chargedStepMomentum, chargedStepChemicalPotential, le_refl, if_true,
    thermalStepA_exp, thermalStepB_exp]
  ring

theorem thermalStep_horizon_frequency_neg (e ell tau : ℝ) :
    thermalStepFrequency e tau - Real.exp e * stringBlackHolePotential ell tau 0 < 0 := by
  rw [thermalStep_horizon_frequency]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (thermalStepScale_pos e tau))
    (thermalRatio_pos tau)) (by norm_num)

/-- Exact reflection amplitude of the constructed interface. -/
theorem thermalStepReflection_formula (e tau : ℝ) :
    thermalStepReflection e tau = 1 / (1 - thermalRatio tau) := by
  rw [thermalStepReflection, chargedStepReflection, thermalStepA_exp, thermalStepB_exp]
  field_simp [(thermalStepScale_pos e tau).ne', (sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

theorem thermalStepTransmission_formula (e tau : ℝ) :
    thermalStepTransmission e tau = (2 - thermalRatio tau) / (1 - thermalRatio tau) := by
  rw [thermalStepTransmission, chargedStepTransmission, thermalStepA_exp, thermalStepB_exp]
  field_simp [(thermalStepScale_pos e tau).ne', (sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

/-- Reflection is inverse normalized black-hole temperature in this calibrated step model. -/
theorem thermalStepReflection_temperature (e ell tau : ℝ) :
    thermalStepReflection e tau = Real.exp ell / (4 * Real.pi * stringBlackHoleTemperature ell tau) := by
  rw [thermalStepReflection_formula, stringBlackHoleTemperature]
  field_simp [Real.pi_ne_zero]

/-- An actual convergent occupation expectation determines the reflection amplitude. -/
theorem thermalStepReflection_occupation (e tau : ℝ) :
    thermalStepReflection e tau = 1 + ∑' n : ℕ, (n : ℝ) * radiationMass tau n := by
  rw [thermalStepReflection_formula, (radiationMass_mean tau).tsum_eq]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

/-- The reflection amplitude also recovers the exact purity of the reduced thermofield state. -/
theorem thermalStepReflection_purity (e tau : ℝ) :
    (∑' n, radiationMass tau n ^ 2) * (2 * thermalStepReflection e tau - 1) = 1 := by
  rw [radiationMass_purity, thermalStepReflection_formula]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne',
    (show 1 + thermalRatio tau ≠ 0 by linarith [thermalRatio_pos tau])]
  ring

/-- Amplification exceeds unity for every finite thermal parameter. -/
theorem thermalStepReflection_amplifies (e tau : ℝ) : 1 < thermalStepReflection e tau ^ 2 :=
  chargedStep_reflection_power_gt_one _ _

theorem thermalStepReflection_power_temperature (e ell tau : ℝ) :
    thermalStepReflection e tau ^ 2 =
      (Real.exp ell / (4 * Real.pi * stringBlackHoleTemperature ell tau)) ^ 2 := by
  rw [thermalStepReflection_temperature e ell tau]

theorem thermalStepWave_contDiff_one (e tau : ℝ) : ContDiff ℝ 1 (thermalStepWave e tau) :=
  chargedStepWave_contDiff_one _ _

theorem thermalStepWave_not_twice_differentiable (e tau : ℝ) :
    ¬ DifferentiableAt ℝ (deriv (thermalStepWave e tau)) 0 :=
  chargedStepWave_not_twice_differentiable _ _

/-- The amplified thermal interface is backed by its actual spatial derivative and current. -/
theorem thermalStepWave_flux (e tau x : ℝ) :
    complexRadialFlux (thermalStepWave e tau) x =
      thermalStepScale e tau * thermalRatio tau / 2 *
        ((2 - thermalRatio tau) / (1 - thermalRatio tau)) ^ 2 := by
  rw [thermalStepWave, chargedStepWave_flux, thermalStepB_exp]
  exact congrArg (fun z : ℝ => thermalStepScale e tau * thermalRatio tau / 2 * z ^ 2)
    (thermalStepTransmission_formula e tau)

theorem thermalStepWave_flux_pos (e tau x : ℝ) :
    0 < complexRadialFlux (thermalStepWave e tau) x :=
  chargedStepWave_flux_pos _ _ _

/-- The true second derivative satisfies the horizon-side charged radial equation. -/
theorem thermalStepWave_horizon_equation (e ell tau u : ℝ) :
    deriv (deriv (thermalStepWave e tau)) (-Real.exp u) +
      ((thermalStepFrequency e tau - Real.exp e * stringBlackHolePotential ell tau 0 : ℝ) : ℂ)^2 *
        thermalStepWave e tau (-Real.exp u) = 0 := by
  rw [thermalStep_horizon_frequency]
  have h := chargedStepWave_second_derivative_left (thermalStepA e tau) (thermalStepB e tau) u
  rw [thermalStepB_exp] at h
  rw [thermalStepWave, h.deriv]
  push_cast
  ring

/-- The same constructed wave solves the free radial equation outside the charged region. -/
theorem thermalStepWave_infinity_equation (e tau u : ℝ) :
    deriv (deriv (thermalStepWave e tau)) (Real.exp u) +
      (thermalStepFrequency e tau : ℂ)^2 * thermalStepWave e tau (Real.exp u) = 0 := by
  rw [thermalStepWave, (chargedStepWave_second_derivative_right _ _ u).deriv]
  unfold thermalStepFrequency
  ring

end GaloisForLFunctions.HTGeometry.CPV
