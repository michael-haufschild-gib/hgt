import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeATransfer
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAStates

/-!
# Actual coexistence parameters at fixed electric charge and coupling

The conserved parameters are Q = exp(w) cos(φ) and α = (exp(w) sin(φ))².
Only the radius ratio, radii, pressure and temperature vary with τ. Explicit
smooth formulas avoid differentiating the auxiliary admissibility angle.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeALargeRadius (w φ τ : ℝ) : ℝ := exp w / sqrt (egbFixedChargeAWeight τ φ)
def egbFixedChargeASmallRadius (w φ τ : ℝ) : ℝ := thermalRatio τ * egbFixedChargeALargeRadius w φ τ
def egbFixedChargeALogScale (w φ τ : ℝ) : ℝ := log (egbFixedChargeALargeRadius w φ τ)
def egbFixedChargeATemperature (w φ τ : ℝ) : ℝ :=
  egbFixedChargeATemperatureWeight τ φ / (4 * Real.pi * egbFixedChargeALargeRadius w φ τ)
def egbFixedChargeAPressure (w φ τ : ℝ) : ℝ :=
  egbFixedChargeAPressureWeight τ φ / (8 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))

theorem egbFixedChargeALargeRadius_pos (w φ τ : ℝ) : 0 < egbFixedChargeALargeRadius w φ τ :=
  div_pos (exp_pos w) (sqrt_pos.mpr (egbFixedChargeAWeight_pos τ φ))

theorem egbFixedChargeA_radii_order (w φ τ : ℝ) :
    0 < egbFixedChargeASmallRadius w φ τ ∧ egbFixedChargeASmallRadius w φ τ < egbFixedChargeALargeRadius w φ τ := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  unfold egbFixedChargeASmallRadius
  exact ⟨mul_pos (thermalRatio_pos τ) hR, mul_lt_of_lt_one_left hR (thermalRatio_lt_one τ)⟩

theorem egbFixedChargeALogScale_exp (w φ τ : ℝ) :
    exp (egbFixedChargeALogScale w φ τ) = egbFixedChargeALargeRadius w φ τ :=
  exp_log (egbFixedChargeALargeRadius_pos w φ τ)

theorem egbFixedChargeA_effective_scale (w φ τ : ℝ) :
    egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAWeight τ φ = exp w ^ (2 : ℕ) := by
  have hs := egbFixedChargeAWeight_pos τ φ
  unfold egbFixedChargeALargeRadius
  rw [div_pow, sq_sqrt hs.le]
  field_simp

theorem egbFixedChargeA_conserved_scale (w φ : ℝ) :
    (exp w * cos φ) ^ (2 : ℕ) + (exp w * sin φ) ^ (2 : ℕ) = exp w ^ (2 : ℕ) := by
  calc
    _ = exp w ^ (2 : ℕ) * (sin φ ^ (2 : ℕ) + cos φ ^ (2 : ℕ)) := by ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

theorem egbFixedChargeA_coupling_square (w φ τ : ℝ) :
    egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) ^ (2 : ℕ) =
      (exp w * sin φ) ^ (2 : ℕ) := by
  rw [egbCoexistenceACouplingRoot_sq, egbFixedChargeALogScale_exp, egbFixedChargeAAngle_coupling]
  unfold egbFixedChargeACouplingWeight egbFixedChargeAFraction
  calc
    _ = (egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAWeight τ φ) * sin φ ^ (2 : ℕ) := by ring
    _ = _ := by rw [egbFixedChargeA_effective_scale]; ring

theorem egbFixedChargeA_charge_square (w φ τ : ℝ) :
    egbCoexistenceACharge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) ^ (2 : ℕ) =
      (exp w * cos φ) ^ (2 : ℕ) := by
  have h := egbCoexistenceA_effective_charge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeALogScale_exp, egbFixedChargeAAngle_charge_weight,
    egbFixedChargeA_effective_scale, egbFixedChargeA_coupling_square] at h
  nlinarith [egbFixedChargeA_conserved_scale w φ]

theorem egbFixedChargeA_large_radius_transfer (w φ τ : ℝ) :
    egbCoexistenceLargeRadius (egbFixedChargeALogScale w φ τ) = egbFixedChargeALargeRadius w φ τ :=
  egbFixedChargeALogScale_exp w φ τ

theorem egbFixedChargeA_small_radius_transfer (w φ τ : ℝ) :
    egbCoexistenceSmallRadius (egbFixedChargeALogScale w φ τ) τ = egbFixedChargeASmallRadius w φ τ := by
  unfold egbCoexistenceSmallRadius egbFixedChargeASmallRadius
  rw [egbFixedChargeALogScale_exp]

theorem egbFixedChargeA_temperature_transfer (w φ τ : ℝ) :
    egbCoexistenceATemperature (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) =
      egbFixedChargeATemperature w φ τ := by
  unfold egbCoexistenceATemperature egbFixedChargeATemperature
  rw [egbFixedChargeAAngle_temperature_weight, egbFixedChargeALogScale_exp]

theorem egbFixedChargeA_pressure_transfer (w φ τ : ℝ) :
    egbCoexistenceAPressure (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) =
      egbFixedChargeAPressure w φ τ := by
  unfold egbCoexistenceAPressure egbFixedChargeAPressure
  rw [egbFixedChargeAAngle_pressure_weight, egbFixedChargeALogScale_exp]

theorem egbFixedChargeATemperature_pos (w φ τ : ℝ) : 0 < egbFixedChargeATemperature w φ τ := by
  rw [← egbFixedChargeA_temperature_transfer]
  exact egbCoexistenceATemperature_pos _ _ _

theorem egbFixedChargeAPressure_pos (w φ τ : ℝ) : 0 < egbFixedChargeAPressure w φ τ := by
  rw [← egbFixedChargeA_pressure_transfer]
  exact egbCoexistenceAPressure_pos _ _ _

end GaloisForLFunctions.HTGeometry
