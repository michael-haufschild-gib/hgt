import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistence
import GaloisForLFunctions.HTGeometry.ThermalAmplificationFluctuations

/-!
# Fixed-charge coexistence and the actual Clapeyron relation

The exact coexistence family from arXiv:2609.00025 section 5 is reparameterized
so charge and Gauss--Bonnet coupling remain fixed along the curve. Pressure and
temperature are differentiated as actual functions of the unrestricted ratio
parameter. Entropy and volume jumps are differences of the corpus state
functions, and volume itself is the actual pressure derivative of enthalpy.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open CPV

/-- Large-radius logarithm that keeps effective charge equal to exp w. -/
def egbFixedChargeLogScale (w tau : ℝ) : ℝ :=
  Real.log (Real.exp w * Real.sqrt (egbCoexistenceShape tau) / thermalRatio tau)

def egbFixedChargePressure (w tau : ℝ) : ℝ :=
  egbCoexistencePressure (egbFixedChargeLogScale w tau) tau

def egbFixedChargeTemperature (w tau : ℝ) : ℝ :=
  egbCoexistenceTemperature (egbFixedChargeLogScale w tau) tau

/-- Thermodynamic volume of a spherical state. -/
def egbThermodynamicVolume (r : ℝ) : ℝ := 4 * Real.pi * r ^ (3 : ℕ) / 3

def egbFixedChargeEntropyJump (w tau : ℝ) : ℝ :=
  egbEntropyB (egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau)) -
    egbEntropyB (egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau)

def egbFixedChargeVolumeJump (w tau : ℝ) : ℝ :=
  egbThermodynamicVolume (egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau)) -
    egbThermodynamicVolume (egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau)

theorem egbFixedChargeLogScale_exp (w tau : ℝ) :
    Real.exp (egbFixedChargeLogScale w tau) =
      Real.exp w * Real.sqrt (egbCoexistenceShape tau) / thermalRatio tau := by
  exact Real.exp_log (div_pos (mul_pos (Real.exp_pos w)
    (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau))) (thermalRatio_pos tau))

theorem egbFixedCharge_effective_scale (w tau : ℝ) :
    egbCoexistenceScale (egbFixedChargeLogScale w tau) tau = Real.exp w := by
  unfold egbCoexistenceScale
  rw [egbFixedChargeLogScale_exp]
  field_simp [(thermalRatio_pos tau).ne', (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau)).ne']

/-- Both conserved parameters are constant along the entire coexistence curve. -/
theorem egbFixedCharge_parameters (w tau theta : ℝ) :
    egbCoexistenceCharge (egbFixedChargeLogScale w tau) tau theta = Real.exp w * Real.cos theta ∧
      egbCoexistenceCouplingRoot (egbFixedChargeLogScale w tau) tau theta = Real.exp w * Real.sin theta := by
  simp only [egbCoexistenceCharge, egbCoexistenceCouplingRoot, egbFixedCharge_effective_scale, and_self]

theorem egbFixedCharge_radii (w tau : ℝ) :
    egbCoexistenceSmallRadius (egbFixedChargeLogScale w tau) tau = Real.exp w * Real.sqrt (egbCoexistenceShape tau) ∧
      egbCoexistenceLargeRadius (egbFixedChargeLogScale w tau) =
        Real.exp w * Real.sqrt (egbCoexistenceShape tau) / thermalRatio tau := by
  constructor
  · unfold egbCoexistenceSmallRadius
    rw [egbFixedChargeLogScale_exp]
    field_simp [(thermalRatio_pos tau).ne']
  · exact egbFixedChargeLogScale_exp w tau

theorem egbFixedChargePressure_formula (w tau : ℝ) :
    egbFixedChargePressure w tau =
      3 * thermalRatio tau ^ (2 : ℕ) / (8 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau ^ (2 : ℕ)) := by
  unfold egbFixedChargePressure egbCoexistencePressure
  rw [egbFixedChargeLogScale_exp]
  simp only [div_pow, mul_pow, Real.sq_sqrt (egbCoexistenceShape_pos tau).le]
  field_simp

theorem egbFixedChargeTemperature_formula (w tau : ℝ) :
    egbFixedChargeTemperature w tau = thermalRatio tau * (1 + thermalRatio tau) /
      (Real.pi * Real.exp w * egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau)) := by
  unfold egbFixedChargeTemperature egbCoexistenceTemperature
  rw [egbFixedChargeLogScale_exp]
  field_simp

/-- Volume is verified as the actual pressure derivative of the existing mass/enthalpy. -/
theorem egbMass_pressure_derivative (P Q a r : ℝ) :
    HasDerivAt (fun p => egbMass p Q a r) (egbThermodynamicVolume r) P := by
  have h : HasDerivAt (fun p => egbMass p Q a r) (0 + 4 * Real.pi * 1 * r ^ (3 : ℕ) / 3) P :=
    (hasDerivAt_const P (r / 2 + (Q^(2 : ℕ) + a^(2 : ℕ)) / (2*r))).add
      ((((hasDerivAt_id P).const_mul (4 * Real.pi)).mul_const (r ^ (3 : ℕ))).div_const 3)
  exact h.congr_deriv (by simp only [zero_add, mul_one, egbThermodynamicVolume])

theorem egbFixedChargeEntropyJump_formula (w tau : ℝ) :
    egbFixedChargeEntropyJump w tau =
      Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau * (1 - thermalRatio tau ^ (2 : ℕ)) / thermalRatio tau ^ (2 : ℕ) := by
  unfold egbFixedChargeEntropyJump
  rw [(egbFixedCharge_radii w tau).1, (egbFixedCharge_radii w tau).2]
  unfold egbEntropyB
  simp only [div_pow, mul_pow, Real.sq_sqrt (egbCoexistenceShape_pos tau).le]
  field_simp [(thermalRatio_pos tau).ne']

theorem egbFixedChargeVolumeJump_formula (w tau : ℝ) :
    egbFixedChargeVolumeJump w tau =
      4 * Real.pi * Real.exp w ^ (3 : ℕ) * egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau) *
        (1 - thermalRatio tau ^ (3 : ℕ)) / (3 * thermalRatio tau ^ (3 : ℕ)) := by
  unfold egbFixedChargeVolumeJump
  rw [(egbFixedCharge_radii w tau).1, (egbFixedCharge_radii w tau).2]
  unfold egbThermodynamicVolume
  have hs : Real.sqrt (egbCoexistenceShape tau) ^ (3 : ℕ) =
      egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau) := by
    rw [pow_succ, Real.sq_sqrt (egbCoexistenceShape_pos tau).le]
  simp only [div_pow, mul_pow, hs]
  field_simp [(thermalRatio_pos tau).ne']

theorem egbFixedChargeEntropyJump_pos (w tau : ℝ) : 0 < egbFixedChargeEntropyJump w tau :=
  egbCoexistence_entropy_jump_pos _ _

theorem egbFixedChargeVolumeJump_pos (w tau : ℝ) : 0 < egbFixedChargeVolumeJump w tau := by
  rw [egbFixedChargeVolumeJump_formula]
  have hc : thermalRatio tau ^ (3 : ℕ) < 1 := pow_lt_one₀ (thermalRatio_pos tau).le (thermalRatio_lt_one tau) (by norm_num)
  have hd := egbCoexistenceShape_pos tau
  have hr := thermalRatio_pos tau
  have hs := Real.sqrt_pos.mpr hd
  positivity


/-- The auxiliary coexistence shape is differentiated through the actual thermal ratio. -/
theorem egbCoexistenceShape_hasDerivAt (tau : ℝ) :
    HasDerivAt egbCoexistenceShape (-Real.exp tau * thermalRatio tau * (2 * thermalRatio tau + 4)) tau := by
  have hr := thermalRatio_hasDerivAt tau
  have h : HasDerivAt egbCoexistenceShape
      (2 * thermalRatio tau ^ (1 : ℕ) * (-Real.exp tau * thermalRatio tau) +
        4 * (-Real.exp tau * thermalRatio tau) + 0) tau :=
    ((hr.pow 2).add (hr.const_mul 4)).add (hasDerivAt_const tau 1)
  exact h.congr_deriv (by ring)

/-- Actual derivative of coexistence pressure while both charge and coupling stay fixed. -/
theorem egbFixedChargePressure_hasDerivAt (w tau : ℝ) :
    HasDerivAt (egbFixedChargePressure w)
      (-3 * Real.exp tau * thermalRatio tau ^ (2 : ℕ) * (1 - thermalRatio tau ^ (2 : ℕ)) /
        (4 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau ^ (3 : ℕ))) tau := by
  rw [show egbFixedChargePressure w = (fun s => 3 * thermalRatio s ^ (2 : ℕ) /
    (8 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape s ^ (2 : ℕ))) from funext (egbFixedChargePressure_formula w)]
  have hn := ((thermalRatio_hasDerivAt tau).pow 2).const_mul 3
  have hd := ((egbCoexistenceShape_hasDerivAt tau).pow 2).const_mul (8 * Real.pi * Real.exp w ^ (2 : ℕ))
  have hne : 8 * Real.pi * Real.exp w ^ (2 : ℕ) * egbCoexistenceShape tau ^ (2 : ℕ) ≠ 0 := by
    have hp := egbCoexistenceShape_pos tau
    positivity
  apply (hn.div hd hne).congr_deriv
  simp only [Pi.pow_apply]
  field_simp [Real.pi_ne_zero, (egbCoexistenceShape_pos tau).ne']
  unfold egbCoexistenceShape
  ring

/-- Actual derivative of coexistence temperature on the same fixed-charge curve. -/
theorem egbFixedChargeTemperature_hasDerivAt (w tau : ℝ) :
    HasDerivAt (egbFixedChargeTemperature w)
      (-Real.exp tau * thermalRatio tau * (1 - thermalRatio tau ^ (3 : ℕ)) /
        (Real.pi * Real.exp w * egbCoexistenceShape tau ^ (2 : ℕ) * Real.sqrt (egbCoexistenceShape tau))) tau := by
  rw [show egbFixedChargeTemperature w = (fun s => thermalRatio s * (1 + thermalRatio s) /
    (Real.pi * Real.exp w * egbCoexistenceShape s * Real.sqrt (egbCoexistenceShape s))) from
      funext (egbFixedChargeTemperature_formula w)]
  have hr := thermalRatio_hasDerivAt tau
  have hd := egbCoexistenceShape_hasDerivAt tau
  have hn := hr.mul ((hasDerivAt_const tau 1).add hr)
  have hb := (hd.const_mul (Real.pi * Real.exp w)).mul (hd.sqrt (egbCoexistenceShape_pos tau).ne')
  have hne : Real.pi * Real.exp w * egbCoexistenceShape tau * Real.sqrt (egbCoexistenceShape tau) ≠ 0 := by
    have hp := egbCoexistenceShape_pos tau
    positivity
  apply (hn.div hb hne).congr_deriv
  simp only [Pi.mul_apply, Pi.add_apply]
  field_simp [Real.pi_ne_zero, (egbCoexistenceShape_pos tau).ne',
    (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau)).ne']
  ring_nf
  simp only [Real.sq_sqrt (egbCoexistenceShape_pos tau).le]
  unfold egbCoexistenceShape
  ring

theorem egbFixedChargePressure_derivative_neg (w tau : ℝ) : deriv (egbFixedChargePressure w) tau < 0 := by
  rw [(egbFixedChargePressure_hasDerivAt w tau).deriv]
  have hr := thermalRatio_pos tau
  have h1 : 0 < 1 - thermalRatio tau ^ (2 : ℕ) := by nlinarith [thermalRatio_lt_one tau]
  have hd := egbCoexistenceShape_pos tau
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos tau)) (sq_pos_of_pos hr)) h1
  · positivity

theorem egbFixedChargeTemperature_derivative_neg (w tau : ℝ) : deriv (egbFixedChargeTemperature w) tau < 0 := by
  rw [(egbFixedChargeTemperature_hasDerivAt w tau).deriv]
  have hr := thermalRatio_pos tau
  have hc : thermalRatio tau ^ (3 : ℕ) < 1 := pow_lt_one₀ hr.le (thermalRatio_lt_one tau) (by norm_num)
  have hd := egbCoexistenceShape_pos tau
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos tau)) hr)
      (sub_pos.mpr hc)
  · positivity

theorem egbFixedChargePressure_strictAnti (w : ℝ) : StrictAnti (egbFixedChargePressure w) :=
  strictAnti_of_deriv_neg (egbFixedChargePressure_derivative_neg w)

theorem egbFixedChargeTemperature_strictAnti (w : ℝ) : StrictAnti (egbFixedChargeTemperature w) :=
  strictAnti_of_deriv_neg (egbFixedChargeTemperature_derivative_neg w)

/-- Exact Clapeyron identity using actual derivatives and actual state-function jumps. -/
theorem egbFixedCharge_clapeyron_cross (w tau : ℝ) :
    deriv (egbFixedChargePressure w) tau * egbFixedChargeVolumeJump w tau =
      deriv (egbFixedChargeTemperature w) tau * egbFixedChargeEntropyJump w tau := by
  rw [(egbFixedChargePressure_hasDerivAt w tau).deriv,
    (egbFixedChargeTemperature_hasDerivAt w tau).deriv,
    egbFixedChargeVolumeJump_formula, egbFixedChargeEntropyJump_formula]
  field_simp [Real.pi_ne_zero, (egbCoexistenceShape_pos tau).ne',
    (thermalRatio_pos tau).ne', (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau)).ne']
  ring_nf
  simp only [Real.sq_sqrt (egbCoexistenceShape_pos tau).le]

/-- The physical coexistence slope is entropy jump divided by thermodynamic volume jump. -/
theorem egbFixedCharge_clapeyron (w tau : ℝ) :
    deriv (egbFixedChargePressure w) tau / deriv (egbFixedChargeTemperature w) tau =
      egbFixedChargeEntropyJump w tau / egbFixedChargeVolumeJump w tau := by
  apply (div_eq_div_iff (egbFixedChargeTemperature_derivative_neg w tau).ne
    (egbFixedChargeVolumeJump_pos w tau).ne').mpr
  exact (egbFixedCharge_clapeyron_cross w tau).trans (mul_comm _ _)

theorem egbFixedCharge_clapeyron_slope_pos (w tau : ℝ) :
    0 < deriv (egbFixedChargePressure w) tau / deriv (egbFixedChargeTemperature w) tau := by
  rw [egbFixedCharge_clapeyron]
  exact div_pos (egbFixedChargeEntropyJump_pos w tau) (egbFixedChargeVolumeJump_pos w tau)

end GaloisForLFunctions.HTGeometry
