import GaloisForLFunctions.HTGeometry.GaussBonnetSmarrAnomaly
import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAGauge

/-!
# Model-A critical states with all positivity conditions discharged

Equations (21)--(24) of arXiv:2609.00025 admit a useful dimensionless
parameter b = α / r_c². Its largest physical value is (2√3-3)/6.
An angular parameter supplies real charge and coupling roots, including
both the zero-charge and zero-coupling endpoints. All theorem parameters
are unrestricted real data, never assumed critical or positive.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbCriticalAMaxShape : ℝ := (2 * sqrt 3 - 3) / 6
def egbCriticalAShape (θ : ℝ) : ℝ := egbCriticalAMaxShape * sin θ ^ (2 : ℕ)
def egbCriticalACouplingRoot (x θ : ℝ) : ℝ := exp x * sqrt egbCriticalAMaxShape * sin θ
def egbCriticalAChargeFactor (θ : ℝ) : ℝ :=
  2 * egbCriticalAMaxShape * (egbCriticalAShape θ + egbCriticalAMaxShape + 1) / (1 + 2 * egbCriticalAShape θ)
def egbCriticalACharge (x θ : ℝ) : ℝ := exp x * cos θ * sqrt (egbCriticalAChargeFactor θ)
def egbCriticalATemperature (x θ : ℝ) : ℝ := 1 / (3 * Real.pi * exp x * (1 + 2 * egbCriticalAShape θ))
def egbCriticalAPressure (x θ : ℝ) : ℝ :=
  (3 - 2 * egbCriticalAShape θ) / (48 * Real.pi * exp x ^ (2 : ℕ) * (1 + 2 * egbCriticalAShape θ))

theorem egbCriticalAMaxShape_bounds : 0 < egbCriticalAMaxShape ∧ egbCriticalAMaxShape < 1 / 6 := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := sqrt_nonneg (3 : ℝ)
  unfold egbCriticalAMaxShape
  constructor <;> nlinarith

theorem egbCriticalAMaxShape_quadratic : 12 * egbCriticalAMaxShape ^ (2 : ℕ) + 12 * egbCriticalAMaxShape - 1 = 0 := by
  have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold egbCriticalAMaxShape
  nlinarith

theorem egbCriticalAShape_bounds (θ : ℝ) :
    0 ≤ egbCriticalAShape θ ∧ egbCriticalAShape θ ≤ egbCriticalAMaxShape := by
  have hp := egbCriticalAMaxShape_bounds.1
  have ht := sin_sq_add_cos_sq θ
  unfold egbCriticalAShape
  constructor
  · positivity
  · nlinarith [sq_nonneg (cos θ), mul_nonneg (le_of_lt hp) (sq_nonneg (cos θ))]

theorem egbCriticalAShape_lt_sixth (θ : ℝ) : egbCriticalAShape θ < 1 / 6 :=
  lt_of_le_of_lt (egbCriticalAShape_bounds θ).2 egbCriticalAMaxShape_bounds.2

theorem egbCriticalAChargeFactor_pos (θ : ℝ) : 0 < egbCriticalAChargeFactor θ := by
  have h₁ := egbCriticalAMaxShape_bounds.1
  have h₂ := (egbCriticalAShape_bounds θ).1
  unfold egbCriticalAChargeFactor
  positivity

theorem egbCriticalA_coupling_square (x θ : ℝ) :
    egbCriticalACouplingRoot x θ ^ (2 : ℕ) = exp x ^ (2 : ℕ) * egbCriticalAShape θ := by
  unfold egbCriticalACouplingRoot egbCriticalAShape
  rw [mul_pow, mul_pow, sq_sqrt (le_of_lt egbCriticalAMaxShape_bounds.1)]
  ring

/-- The angular construction satisfies the exact critical effective-charge equation. -/
theorem egbCriticalA_effective_charge (x θ : ℝ) :
    egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) =
      exp x ^ (2 : ℕ) * (1 - 6 * egbCriticalAShape θ) / (6 * (1 + 2 * egbCriticalAShape θ)) := by
  rw [egbCriticalA_coupling_square]
  unfold egbCriticalACharge
  rw [mul_pow, mul_pow, sq_sqrt (le_of_lt (egbCriticalAChargeFactor_pos θ))]
  have hc : cos θ ^ (2 : ℕ) = 1 - sin θ ^ (2 : ℕ) := by nlinarith [sin_sq_add_cos_sq θ]
  rw [hc]
  unfold egbCriticalAChargeFactor egbCriticalAShape
  have hd : 1 + 2 * (egbCriticalAMaxShape * sin θ ^ (2 : ℕ)) ≠ 0 := by
    have h := egbCriticalAMaxShape_bounds.1
    positivity
  have hm := egbCriticalAMaxShape_bounds.1
  field_simp
  have hb := egbCriticalAMaxShape_quadratic
  linear_combination hb

theorem egbCriticalA_effective_charge_pos (x θ : ℝ) :
    0 < egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) := by
  rw [egbCriticalA_effective_charge]
  have h₁ := (egbCriticalAShape_bounds θ).1
  have h₂ : 0 < 1 - 6 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  positivity

theorem egbCriticalATemperature_pos (x θ : ℝ) : 0 < egbCriticalATemperature x θ := by
  have h := (egbCriticalAShape_bounds θ).1
  unfold egbCriticalATemperature
  positivity

theorem egbCriticalAPressure_pos (x θ : ℝ) : 0 < egbCriticalAPressure x θ := by
  have h₁ := (egbCriticalAShape_bounds θ).1
  have h₂ : 0 < 3 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  unfold egbCriticalAPressure
  positivity

/-- The critical-radius polynomial obtained by eliminating temperature from the inflection conditions. -/
theorem egbCriticalA_radius_polynomial (x θ : ℝ) :
    exp x ^ (4 : ℕ) - 6 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) * exp x ^ (2 : ℕ) -
      12 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ)) = 0 := by
  have he : egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) =
      (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ)) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) := by ring
  rw [he, egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  have hd : 1 + 2 * egbCriticalAShape θ ≠ 0 := by
    have h := (egbCriticalAShape_bounds θ).1
    positivity
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp
  ring

/-- Positive branch of the square root in the paper's closed critical-radius formula. -/
theorem egbCriticalA_radius_root_gap (x θ : ℝ) :
    0 < exp x ^ (2 : ℕ) - 3 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) := by
  have hd : 1 + 2 * egbCriticalAShape θ ≠ 0 := by
    have h := (egbCriticalAShape_bounds θ).1
    positivity
  have he : exp x ^ (2 : ℕ) - 3 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) =
      exp x ^ (2 : ℕ) * (1 - 2 * egbCriticalAShape θ) * (1 + 6 * egbCriticalAShape θ) / (2 * (1 + 2 * egbCriticalAShape θ)) := by
    have hc : egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) =
        (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ)) + egbCriticalACouplingRoot x θ ^ (2 : ℕ) := by ring
    rw [hc, egbCriticalA_effective_charge, egbCriticalA_coupling_square]
    have hb := (egbCriticalAShape_bounds θ).1
    field_simp
    ring
  rw [he]
  have h₁ := (egbCriticalAShape_bounds θ).1
  have h₂ : 0 < 1 - 2 * egbCriticalAShape θ := by linarith [egbCriticalAShape_lt_sixth θ]
  positivity

/-- Equation (22), verified with the actual constructed charge and coupling. -/
theorem egbCriticalA_radius_formula (x θ : ℝ) :
    exp x ^ (2 : ℕ) = 3 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) +
      sqrt (9 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) ^ (2 : ℕ) +
        12 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ))) := by
  have he : 9 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) ^ (2 : ℕ) +
      12 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ)) =
      (exp x ^ (2 : ℕ) - 3 * (egbCriticalACharge x θ ^ (2 : ℕ) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ))) ^ (2 : ℕ) := by
    nlinarith [egbCriticalA_radius_polynomial x θ]
  rw [he, sqrt_sq_eq_abs, abs_of_pos (egbCriticalA_radius_root_gap x θ)]
  ring

theorem egbCriticalA_temperature_formula (x θ : ℝ) :
    egbCriticalATemperature x θ =
      (exp x ^ (2 : ℕ) - 2 * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ))) /
        (2 * Real.pi * exp x * (exp x ^ (2 : ℕ) + 6 * egbCriticalACouplingRoot x θ ^ (2 : ℕ))) := by
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  have h := (egbCriticalAShape_bounds θ).1
  have h₁ : 1 + 2 * egbCriticalAShape θ ≠ 0 := by positivity
  have h₂ : exp x ^ (2 : ℕ) + 6 * (exp x ^ (2 : ℕ) * egbCriticalAShape θ) ≠ 0 := by positivity
  unfold egbCriticalATemperature
  field_simp
  ring

theorem egbCriticalA_pressure_value (x θ : ℝ) :
    egbPressureA (egbCriticalATemperature x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp x) =
      egbCriticalAPressure x θ := by
  unfold egbPressureA
  rw [egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  have hd : 1 + 2 * egbCriticalAShape θ ≠ 0 := by
    have h := (egbCriticalAShape_bounds θ).1
    positivity
  unfold egbCriticalATemperature egbCriticalAPressure
  field_simp
  ring

/-- The actual surface-gravity temperature attains the constructed critical value. -/
theorem egbCriticalA_temperature_value (x θ : ℝ) :
    egbTemperatureA (egbCriticalAPressure x θ) (egbCriticalACharge x θ) (egbCriticalACouplingRoot x θ) (exp x) =
      egbCriticalATemperature x θ := by
  rw [← egbCriticalA_pressure_value, egbTemperatureA_pressure]

/-- Equation (24) agrees with the positive pressure obtained from the equation of state. -/
theorem egbCriticalA_pressure_formula (x θ : ℝ) :
    egbCriticalAPressure x θ =
      (exp x ^ (4 : ℕ) - (3 * egbCriticalACharge x θ ^ (2 : ℕ) + 5 * egbCriticalACouplingRoot x θ ^ (2 : ℕ)) * exp x ^ (2 : ℕ) -
        2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ))) /
          (8 * Real.pi * exp x ^ (4 : ℕ) * (exp x ^ (2 : ℕ) + 6 * egbCriticalACouplingRoot x θ ^ (2 : ℕ))) := by
  have he : 3 * egbCriticalACharge x θ ^ (2 : ℕ) + 5 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) =
      3 * (egbCriticalACharge x θ ^ (2 : ℕ) + egbCriticalACouplingRoot x θ ^ (2 : ℕ)) + 2 * egbCriticalACouplingRoot x θ ^ (2 : ℕ) := by ring
  rw [he, egbCriticalA_effective_charge, egbCriticalA_coupling_square]
  have hb := (egbCriticalAShape_bounds θ).1
  unfold egbCriticalAPressure
  field_simp
  ring

/-- Every physically admissible dimensionless coupling occurs in the angular construction. -/
theorem egbCriticalAShape_range (b : ℝ) :
    (∃ θ : ℝ, egbCriticalAShape θ = b) ↔ 0 ≤ b ∧ b ≤ egbCriticalAMaxShape := by
  constructor
  · rintro ⟨θ, rfl⟩
    exact egbCriticalAShape_bounds θ
  · intro hb
    have hm := egbCriticalAMaxShape_bounds.1
    have hq : 0 ≤ b / egbCriticalAMaxShape := div_nonneg hb.1 (le_of_lt hm)
    have hq₁ : b / egbCriticalAMaxShape ≤ 1 := (div_le_iff₀ hm).2 (by simpa using hb.2)
    have hs : sqrt (b / egbCriticalAMaxShape) ≤ 1 := by
      nlinarith [sq_sqrt hq, sqrt_nonneg (b / egbCriticalAMaxShape)]
    refine ⟨arcsin (sqrt (b / egbCriticalAMaxShape)), ?_⟩
    unfold egbCriticalAShape
    rw [sin_arcsin (by linarith [sqrt_nonneg (b / egbCriticalAMaxShape)]) hs, sq_sqrt hq]
    field_simp

end GaloisForLFunctions.HTGeometry
