import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAReduced
import GaloisForLFunctions.HTGeometry.GaussBonnetSmarrAnomaly

/-!
# Physical states of model-A coexistence

Lift the positive reduced weights to actual charge, Gauss–Bonnet coupling,
pressure and temperature. All input parameters are unrestricted reals.
The two phase radii solve the actual equation of state, including the
zero-charge endpoint of the allowed coupling range.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceATemperature (k τ θ : ℝ) : ℝ :=
  egbCoexistenceATemperatureWeight τ θ / (4 * Real.pi * exp k)

def egbCoexistenceAPressure (k τ θ : ℝ) : ℝ :=
  egbCoexistenceAPressureWeight τ θ / (8 * Real.pi * exp k ^ 2)

def egbCoexistenceACouplingRoot (k τ θ : ℝ) : ℝ :=
  exp k * sqrt (egbCoexistenceAMaxCoupling τ) * sin θ

def egbCoexistenceACharge (k τ θ : ℝ) : ℝ :=
  exp k * cos θ * sqrt (egbCoexistenceAChargeFactor τ θ)

theorem egbCoexistenceATemperature_pos (k τ θ : ℝ) : 0 < egbCoexistenceATemperature k τ θ := by
  have h := egbCoexistenceATemperatureWeight_pos τ θ
  unfold egbCoexistenceATemperature
  positivity

theorem egbCoexistenceAPressure_pos (k τ θ : ℝ) : 0 < egbCoexistenceAPressure k τ θ := by
  have h := egbCoexistenceAPressureWeight_pos τ θ
  unfold egbCoexistenceAPressure
  positivity

theorem egbCoexistenceACouplingRoot_sq (k τ θ : ℝ) :
    egbCoexistenceACouplingRoot k τ θ ^ 2 = exp k ^ 2 * egbCoexistenceACouplingWeight τ θ := by
  unfold egbCoexistenceACouplingRoot egbCoexistenceACouplingWeight
  rw [mul_pow, mul_pow, sq_sqrt (le_of_lt (egbCoexistenceAMaxCoupling_pos τ))]
  ring

theorem egbCoexistenceACharge_sq (k τ θ : ℝ) :
    egbCoexistenceACharge k τ θ ^ 2 =
      exp k ^ 2 * (egbCoexistenceAChargeWeight τ θ - egbCoexistenceACouplingWeight τ θ) := by
  rw [egbCoexistenceAChargeWeight_factorization]
  unfold egbCoexistenceACharge
  rw [mul_pow, mul_pow, sq_sqrt (le_of_lt (egbCoexistenceAChargeFactor_pos τ θ))]
  ring

theorem egbCoexistenceA_effective_charge (k τ θ : ℝ) :
    egbCoexistenceACharge k τ θ ^ 2 + egbCoexistenceACouplingRoot k τ θ ^ 2 =
      exp k ^ 2 * egbCoexistenceAChargeWeight τ θ := by
  rw [egbCoexistenceACharge_sq, egbCoexistenceACouplingRoot_sq]
  ring

/-- Vanishing electric charge occurs precisely at maximal coupling weight. -/
theorem egbCoexistenceACharge_zero_iff (k τ θ : ℝ) :
    egbCoexistenceACharge k τ θ = 0 ↔ cos θ = 0 := by
  have hR := exp_ne_zero k
  have hF := ne_of_gt (sqrt_pos.mpr (egbCoexistenceAChargeFactor_pos τ θ))
  unfold egbCoexistenceACharge
  simp only [mul_eq_zero, hR, hF, false_or, or_false]

/-- Actual equation-of-state residual at every positive radius. -/
theorem egbCoexistenceA_pressure_residual (k τ θ u : ℝ) :
    egbPressureA (egbCoexistenceATemperature k τ θ) (egbCoexistenceACharge k τ θ)
        (egbCoexistenceACouplingRoot k τ θ) (exp k * exp u) - egbCoexistenceAPressure k τ θ =
      -egbCoexistenceARadialPolynomial τ θ (exp u) / (8 * Real.pi * exp k ^ 2 * exp u ^ 4) := by
  unfold egbPressureA
  rw [egbCoexistenceA_effective_charge, egbCoexistenceACouplingRoot_sq]
  unfold egbCoexistenceATemperature egbCoexistenceAPressure egbCoexistenceARadialPolynomial
  field_simp
  ring

theorem egbCoexistenceA_large_pressure (k τ θ : ℝ) :
    egbPressureA (egbCoexistenceATemperature k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceLargeRadius k) = egbCoexistenceAPressure k τ θ := by
  have h := egbCoexistenceA_pressure_residual k τ θ 0
  simp only [exp_zero, mul_one, egbCoexistenceA_stationarity_large, neg_zero, zero_div] at h
  exact sub_eq_zero.mp h

theorem egbCoexistenceA_small_pressure (k τ θ : ℝ) :
    egbPressureA (egbCoexistenceATemperature k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceSmallRadius k τ) = egbCoexistenceAPressure k τ θ := by
  have h := egbCoexistenceA_pressure_residual k τ θ (log (thermalRatio τ))
  simp only [exp_log (thermalRatio_pos τ), egbCoexistenceA_stationarity_small, neg_zero, zero_div] at h
  simpa only [egbCoexistenceSmallRadius, mul_comm (exp k)] using sub_eq_zero.mp h

theorem egbCoexistenceA_large_temperature (k τ θ : ℝ) :
    egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceLargeRadius k) = egbCoexistenceATemperature k τ θ := by
  rw [← egbCoexistenceA_large_pressure]
  exact egbTemperatureA_pressure _ _ _ k

theorem egbCoexistenceA_small_temperature (k τ θ : ℝ) :
    egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) (egbCoexistenceSmallRadius k τ) = egbCoexistenceATemperature k τ θ := by
  rw [← egbCoexistenceA_small_pressure]
  have hr : egbCoexistenceSmallRadius k τ = exp (k + log (thermalRatio τ)) := by
    rw [exp_add, exp_log (thermalRatio_pos τ), egbCoexistenceSmallRadius, mul_comm]
  rw [hr]
  exact egbTemperatureA_pressure _ _ _ _

end GaloisForLFunctions.HTGeometry
