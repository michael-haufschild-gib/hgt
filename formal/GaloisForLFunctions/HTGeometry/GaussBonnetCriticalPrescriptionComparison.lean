import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAEOS

/-!
# Comparing critical prescriptions at identical charge and coupling

Apply equation (25) of arXiv:2609.00025 to the actual charges and couplings
of the model-A critical family. Prove exact radius, temperature, and pressure
ratios. Model A has larger critical radius and smaller critical temperature
and pressure whenever coupling is nonzero, for every charge in this family.
The zero-coupling boundary gives equality in all three comparisons.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbMatchedCriticalBRadius (x θ : ℝ) : ℝ :=
  sqrt (6 * (egbCriticalACharge x θ ^ 2 + egbCriticalACouplingRoot x θ ^ 2))
def egbMatchedCriticalBTemperature (x θ : ℝ) : ℝ := 1 / (3 * Real.pi * egbMatchedCriticalBRadius x θ)
def egbMatchedCriticalBPressure (x θ : ℝ) : ℝ :=
  1 / (96 * Real.pi * (egbCriticalACharge x θ ^ 2 + egbCriticalACouplingRoot x θ ^ 2))
def egbCriticalBRadiusRatio (θ : ℝ) : ℝ :=
  sqrt ((1 - 6 * egbCriticalAShape θ) / (1 + 2 * egbCriticalAShape θ))

theorem egbMatchedCriticalBRadius_pos (x θ : ℝ) : 0 < egbMatchedCriticalBRadius x θ := by
  have h := egbCriticalA_effective_charge_pos x θ
  unfold egbMatchedCriticalBRadius
  positivity

theorem egbMatchedCriticalBRadius_square (x θ : ℝ) :
    egbMatchedCriticalBRadius x θ ^ 2 = 6 * (egbCriticalACharge x θ ^ 2 + egbCriticalACouplingRoot x θ ^ 2) := by
  unfold egbMatchedCriticalBRadius
  apply sq_sqrt
  have h := egbCriticalA_effective_charge_pos x θ
  positivity

theorem egbMatchedCriticalBTemperature_pos (x θ : ℝ) : 0 < egbMatchedCriticalBTemperature x θ := by
  have h := egbMatchedCriticalBRadius_pos x θ
  unfold egbMatchedCriticalBTemperature
  positivity

theorem egbMatchedCriticalBPressure_pos (x θ : ℝ) : 0 < egbMatchedCriticalBPressure x θ := by
  have h := egbCriticalA_effective_charge_pos x θ
  unfold egbMatchedCriticalBPressure
  positivity

theorem egbCriticalBRadiusRatio_pos (θ : ℝ) : 0 < egbCriticalBRadiusRatio θ := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hn : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  unfold egbCriticalBRadiusRatio
  positivity

theorem egbCriticalBRadiusRatio_square (θ : ℝ) :
    egbCriticalBRadiusRatio θ ^ 2 = (1 - 6 * egbCriticalAShape θ) / (1 + 2 * egbCriticalAShape θ) := by
  unfold egbCriticalBRadiusRatio
  apply sq_sqrt
  have hb := (egbCriticalAShape_bounds θ).1
  have hn : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  positivity

theorem egbCriticalBRadiusRatio_le_one (θ : ℝ) : egbCriticalBRadiusRatio θ ≤ 1 := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hd : 0 < 1 + 2 * egbCriticalAShape θ := by positivity
  have hq : (1 - 6 * egbCriticalAShape θ) / (1 + 2 * egbCriticalAShape θ) ≤ 1 :=
    (div_le_one hd).2 (by linarith)
  nlinarith [egbCriticalBRadiusRatio_square θ, egbCriticalBRadiusRatio_pos θ]

theorem egbCriticalBRadiusRatio_eq_one_iff (θ : ℝ) :
    egbCriticalBRadiusRatio θ = 1 ↔ egbCriticalAShape θ = 0 := by
  constructor
  · intro h
    have hs := egbCriticalBRadiusRatio_square θ
    rw [h, one_pow] at hs
    have hd : 1 + 2 * egbCriticalAShape θ ≠ 0 := by
      have hb := (egbCriticalAShape_bounds θ).1
      positivity
    have he := (div_eq_iff hd).1 hs.symm
    linarith
  · intro h
    simp [egbCriticalBRadiusRatio, h]

theorem egbCriticalBRadiusRatio_lt_one_iff (θ : ℝ) :
    egbCriticalBRadiusRatio θ < 1 ↔ 0 < egbCriticalAShape θ := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hr := egbCriticalBRadiusRatio_le_one θ
  have he := egbCriticalBRadiusRatio_eq_one_iff θ
  constructor
  · intro h
    by_contra hn
    have h₀ : egbCriticalAShape θ = 0 := by linarith
    linarith [he.2 h₀]
  · intro h
    by_contra hn
    have h₀ : egbCriticalBRadiusRatio θ = 1 := by linarith
    linarith [he.1 h₀]

/-- The paper's square-root radius equals a simple factor times the model-A radius. -/
theorem egbMatchedCriticalBRadius_formula (x θ : ℝ) :
    egbMatchedCriticalBRadius x θ = exp x * egbCriticalBRadiusRatio θ := by
  have hs : egbMatchedCriticalBRadius x θ ^ 2 = (exp x * egbCriticalBRadiusRatio θ) ^ 2 := by
    rw [egbMatchedCriticalBRadius_square, egbCriticalA_effective_charge, mul_pow, egbCriticalBRadiusRatio_square]
    have hb := (egbCriticalAShape_bounds θ).1
    field_simp
  have h₁ := egbMatchedCriticalBRadius_pos x θ
  have h₂ : 0 < exp x * egbCriticalBRadiusRatio θ := mul_pos (exp_pos x) (egbCriticalBRadiusRatio_pos θ)
  nlinarith

theorem egbMatchedCriticalBPressure_formula (x θ : ℝ) :
    egbMatchedCriticalBPressure x θ =
      (1 + 2 * egbCriticalAShape θ) / (16 * Real.pi * exp x ^ 2 * (1 - 6 * egbCriticalAShape θ)) := by
  unfold egbMatchedCriticalBPressure
  rw [egbCriticalA_effective_charge]
  have hb := (egbCriticalAShape_bounds θ).1
  have hn : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  field_simp
  ring

theorem egbCriticalA_to_B_temperature_ratio (x θ : ℝ) :
    egbCriticalATemperature x θ / egbMatchedCriticalBTemperature x θ =
      egbCriticalBRadiusRatio θ / (1 + 2 * egbCriticalAShape θ) := by
  unfold egbCriticalATemperature egbMatchedCriticalBTemperature
  rw [egbMatchedCriticalBRadius_formula]
  have hb := (egbCriticalAShape_bounds θ).1
  have hr := egbCriticalBRadiusRatio_pos θ
  field_simp

theorem egbCriticalA_to_B_pressure_ratio (x θ : ℝ) :
    egbCriticalAPressure x θ / egbMatchedCriticalBPressure x θ =
      (3 - 2 * egbCriticalAShape θ) * (1 - 6 * egbCriticalAShape θ) /
        (3 * (1 + 2 * egbCriticalAShape θ) ^ 2) := by
  rw [egbMatchedCriticalBPressure_formula]
  unfold egbCriticalAPressure
  have hb := (egbCriticalAShape_bounds θ).1
  have hn : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  field_simp
  ring

theorem egbCriticalA_radius_ge_B (x θ : ℝ) : egbMatchedCriticalBRadius x θ ≤ exp x := by
  rw [egbMatchedCriticalBRadius_formula]
  have h := mul_le_mul_of_nonneg_left (egbCriticalBRadiusRatio_le_one θ) (le_of_lt (exp_pos x))
  simpa only [mul_one] using h

theorem egbCriticalA_temperature_le_B (x θ : ℝ) : egbCriticalATemperature x θ ≤ egbMatchedCriticalBTemperature x θ := by
  rw [← div_le_one (egbMatchedCriticalBTemperature_pos x θ), egbCriticalA_to_B_temperature_ratio]
  have hb := (egbCriticalAShape_bounds θ).1
  rw [div_le_one (by positivity : 0 < 1 + 2 * egbCriticalAShape θ)]
  linarith [egbCriticalBRadiusRatio_le_one θ]

theorem egbCriticalA_pressure_le_B (x θ : ℝ) : egbCriticalAPressure x θ ≤ egbMatchedCriticalBPressure x θ := by
  rw [← div_le_one (egbMatchedCriticalBPressure_pos x θ), egbCriticalA_to_B_pressure_ratio]
  have hb := (egbCriticalAShape_bounds θ).1
  rw [div_le_one (by positivity : 0 < 3 * (1 + 2 * egbCriticalAShape θ) ^ 2)]
  nlinarith

theorem egbCriticalA_radius_gt_B_iff (x θ : ℝ) :
    egbMatchedCriticalBRadius x θ < exp x ↔ 0 < egbCriticalAShape θ := by
  rw [egbMatchedCriticalBRadius_formula]
  have h := (mul_lt_mul_iff_right₀ (exp_pos x) :
    exp x * egbCriticalBRadiusRatio θ < exp x * 1 ↔ egbCriticalBRadiusRatio θ < 1)
  simpa only [mul_one] using h.trans (egbCriticalBRadiusRatio_lt_one_iff θ)

theorem egbCriticalA_temperature_lt_B_iff (x θ : ℝ) :
    egbCriticalATemperature x θ < egbMatchedCriticalBTemperature x θ ↔ 0 < egbCriticalAShape θ := by
  rw [← div_lt_one (egbMatchedCriticalBTemperature_pos x θ), egbCriticalA_to_B_temperature_ratio]
  have hb := (egbCriticalAShape_bounds θ).1
  rw [div_lt_one (by positivity : 0 < 1 + 2 * egbCriticalAShape θ)]
  constructor
  · intro h
    by_contra hn
    have h₀ : egbCriticalAShape θ = 0 := by linarith
    linarith [(egbCriticalBRadiusRatio_eq_one_iff θ).2 h₀]
  · intro h
    linarith [egbCriticalBRadiusRatio_le_one θ]

theorem egbCriticalA_pressure_lt_B_iff (x θ : ℝ) :
    egbCriticalAPressure x θ < egbMatchedCriticalBPressure x θ ↔ 0 < egbCriticalAShape θ := by
  rw [← div_lt_one (egbMatchedCriticalBPressure_pos x θ), egbCriticalA_to_B_pressure_ratio]
  have hb := (egbCriticalAShape_bounds θ).1
  rw [div_lt_one (by positivity : 0 < 3 * (1 + 2 * egbCriticalAShape θ) ^ 2)]
  constructor <;> intro h <;> nlinarith

theorem egbCriticalA_shape_pos_iff_coupling_nonzero (x θ : ℝ) :
    0 < egbCriticalAShape θ ↔ egbCriticalACouplingRoot x θ ≠ 0 := by
  rw [← sq_pos_iff, egbCriticalA_coupling_square, mul_pos_iff_of_pos_left (by positivity : 0 < exp x ^ 2)]

/-- All three prescription shifts are strict exactly when the actual coupling is nonzero. -/
theorem egbCritical_prescriptions_strict_iff (x θ : ℝ) :
    (egbMatchedCriticalBRadius x θ < exp x ∧
      egbCriticalATemperature x θ < egbMatchedCriticalBTemperature x θ ∧
      egbCriticalAPressure x θ < egbMatchedCriticalBPressure x θ) ↔ egbCriticalACouplingRoot x θ ≠ 0 := by
  rw [egbCriticalA_radius_gt_B_iff, egbCriticalA_temperature_lt_B_iff, egbCriticalA_pressure_lt_B_iff,
    egbCriticalA_shape_pos_iff_coupling_nonzero x θ]
  simp

/-- The unchanged charge/coupling data satisfy the model-B equation of state at its critical values. -/
theorem egbMatchedCriticalB_pressure_value (x θ : ℝ) :
    egbPressureB (egbMatchedCriticalBTemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ)
      (egbMatchedCriticalBRadius x θ) = egbMatchedCriticalBPressure x θ := by
  have he : egbCriticalACharge x θ ^ 2 + egbCriticalACouplingRoot x θ ^ 2 = egbMatchedCriticalBRadius x θ ^ 2 / 6 := by
    rw [egbMatchedCriticalBRadius_square]
    ring
  unfold egbPressureB egbMatchedCriticalBTemperature egbMatchedCriticalBPressure
  rw [he]
  have hp := egbMatchedCriticalBRadius_pos x θ
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
