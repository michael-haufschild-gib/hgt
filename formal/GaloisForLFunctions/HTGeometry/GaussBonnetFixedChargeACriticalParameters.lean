import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalWeights
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAParameters

/-!
# Actual critical state at fixed electric charge and coupling

Match the critical root to the corpus's existing model-A critical family
using exact charge and coupling squares. The radius satisfies the paper's
closed radical formula for the same conserved physical parameters as the
coexistence curve.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalRadius (w φ : ℝ) : ℝ := exp w / sqrt (egbFixedChargeACriticalWeight φ)
def egbFixedChargeACriticalLogScale (w φ : ℝ) : ℝ := log (egbFixedChargeACriticalRadius w φ)
def egbFixedChargeACriticalTemperature (w φ : ℝ) : ℝ :=
  1 / (3 * Real.pi * egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))
def egbFixedChargeACriticalPressure (w φ : ℝ) : ℝ :=
  (3 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (48 * Real.pi * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeACriticalRadius_pos (w φ : ℝ) : 0 < egbFixedChargeACriticalRadius w φ :=
  div_pos (exp_pos w) (sqrt_pos.mpr (egbFixedChargeACriticalWeight_pos φ))

theorem egbFixedChargeACriticalLogScale_exp (w φ : ℝ) :
    exp (egbFixedChargeACriticalLogScale w φ) = egbFixedChargeACriticalRadius w φ :=
  exp_log (egbFixedChargeACriticalRadius_pos w φ)

theorem egbFixedChargeACritical_effective_scale (w φ : ℝ) :
    egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * egbFixedChargeACriticalWeight φ = exp w ^ (2 : ℕ) := by
  have hs := egbFixedChargeACriticalWeight_pos φ
  unfold egbFixedChargeACriticalRadius
  rw [div_pow, sq_sqrt hs.le]
  field_simp

theorem egbFixedChargeACritical_coupling_square (w φ : ℝ) :
    egbCriticalACouplingRoot (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) ^ (2 : ℕ) =
      (exp w * sin φ) ^ (2 : ℕ) := by
  rw [egbCriticalA_coupling_square, egbFixedChargeACriticalLogScale_exp, egbFixedChargeACriticalAngle_shape]
  unfold egbFixedChargeACriticalCouplingWeight egbFixedChargeAFraction
  calc
    _ = (egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * egbFixedChargeACriticalWeight φ) * sin φ ^ (2 : ℕ) := by ring
    _ = _ := by rw [egbFixedChargeACritical_effective_scale]; ring

theorem egbFixedChargeACritical_charge_square (w φ : ℝ) :
    egbCriticalACharge (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) ^ (2 : ℕ) =
      (exp w * cos φ) ^ (2 : ℕ) := by
  have h := egbCriticalA_effective_charge (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACriticalAngle_shape] at h
  have he : egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * (1 - 6 * egbFixedChargeACriticalCouplingWeight φ) /
      (6 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) = exp w ^ (2 : ℕ) := by
    calc
      _ = egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) * egbFixedChargeACriticalWeight φ := by
        rw [egbFixedChargeACriticalWeight_formula]
        ring
      _ = _ := egbFixedChargeACritical_effective_scale w φ
  rw [he, egbFixedChargeACritical_coupling_square] at h
  nlinarith [egbFixedChargeA_conserved_scale w φ]

theorem egbFixedChargeACritical_temperature_transfer (w φ : ℝ) :
    egbCriticalATemperature (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) =
      egbFixedChargeACriticalTemperature w φ := by
  unfold egbCriticalATemperature egbFixedChargeACriticalTemperature
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACriticalAngle_shape]

theorem egbFixedChargeACritical_pressure_transfer (w φ : ℝ) :
    egbCriticalAPressure (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ) =
      egbFixedChargeACriticalPressure w φ := by
  unfold egbCriticalAPressure egbFixedChargeACriticalPressure
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACriticalAngle_shape]

theorem egbFixedChargeACriticalTemperature_pos (w φ : ℝ) : 0 < egbFixedChargeACriticalTemperature w φ := by
  rw [← egbFixedChargeACritical_temperature_transfer]
  exact egbCriticalATemperature_pos _ _

theorem egbFixedChargeACriticalPressure_pos (w φ : ℝ) : 0 < egbFixedChargeACriticalPressure w φ := by
  rw [← egbFixedChargeACritical_pressure_transfer]
  exact egbCriticalAPressure_pos _ _

/-- Equation (22) at precisely the fixed physical charge and coupling of the coexistence path. -/
theorem egbFixedChargeACritical_radius_formula (w φ : ℝ) :
    egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) =
      3 * ((exp w * cos φ) ^ (2 : ℕ) + 2 * (exp w * sin φ) ^ (2 : ℕ)) +
        sqrt (9 * ((exp w * cos φ) ^ (2 : ℕ) + 2 * (exp w * sin φ) ^ (2 : ℕ)) ^ (2 : ℕ) +
          12 * (exp w * sin φ) ^ (2 : ℕ) * ((exp w * cos φ) ^ (2 : ℕ) + (exp w * sin φ) ^ (2 : ℕ))) := by
  have h := egbCriticalA_radius_formula (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACritical_charge_square, egbFixedChargeACritical_coupling_square] at h
  exact h

theorem egbFixedChargeACritical_radius_polynomial (w φ : ℝ) :
    egbFixedChargeACriticalRadius w φ ^ (4 : ℕ) -
      6 * ((exp w * cos φ) ^ (2 : ℕ) + 2 * (exp w * sin φ) ^ (2 : ℕ)) * egbFixedChargeACriticalRadius w φ ^ (2 : ℕ) -
        12 * (exp w * sin φ) ^ (2 : ℕ) * ((exp w * cos φ) ^ (2 : ℕ) + (exp w * sin φ) ^ (2 : ℕ)) = 0 := by
  have h := egbCriticalA_radius_polynomial (egbFixedChargeACriticalLogScale w φ) (egbFixedChargeACriticalAngle φ)
  rw [egbFixedChargeACriticalLogScale_exp, egbFixedChargeACritical_charge_square, egbFixedChargeACritical_coupling_square] at h
  exact h

end GaloisForLFunctions.HTGeometry
