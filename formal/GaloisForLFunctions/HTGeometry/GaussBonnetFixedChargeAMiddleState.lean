import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanHeatAmplitude

/-!
# The actual unstable equilibrium between the fixed-charge phases

Transfer the paper's explicit intermediate stationary root to conserved
physical charge and coupling. Its temperature equals the coexistence
value, its heat capacity is negative, and its Gibbs barrier is positive.
The radius converges to the same critical radius as both stable phases.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAMiddleRadius (w φ τ : ℝ) : ℝ :=
  egbFixedChargeALargeRadius w φ τ * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)

def egbFixedChargeAGibbsBarrier (w φ τ l : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMiddleRadius w φ τ) -
    egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)

theorem egbFixedChargeAMiddleRadius_pos (w φ τ : ℝ) : 0 < egbFixedChargeAMiddleRadius w φ τ :=
  mul_pos (egbFixedChargeALargeRadius_pos w φ τ) (egbCoexistenceAMiddleRadius_pos τ (egbFixedChargeAAngle τ φ))

theorem egbFixedChargeAMiddleRadius_bounds (w φ τ : ℝ) :
    egbFixedChargeASmallRadius w φ τ < egbFixedChargeAMiddleRadius w φ τ ∧
      egbFixedChargeAMiddleRadius w φ τ < egbFixedChargeALargeRadius w φ τ := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have h := egbCoexistenceAMiddleRadius_bounds τ (egbFixedChargeAAngle τ φ)
  constructor
  · simpa only [egbFixedChargeASmallRadius, egbFixedChargeAMiddleRadius, mul_comm] using mul_lt_mul_of_pos_left h.1 hR
  · simpa only [egbFixedChargeAMiddleRadius, mul_one] using mul_lt_mul_of_pos_left h.2 hR

theorem egbFixedChargeA_middle_temperature (w φ τ : ℝ) :
    egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeAMiddleRadius w φ τ) =
      egbFixedChargeATemperature w φ τ := by
  have h := egbCoexistenceA_middle_temperature (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeALogScale_exp, egbFixedChargeA_temperature_transfer] at h
  exact h

theorem egbFixedChargeA_middle_thermal_slope_neg (w φ τ : ℝ) :
    deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeAMiddleRadius w φ τ) < 0 := by
  have h := egbCoexistenceA_middle_thermal_slope_neg (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeALogScale_exp] at h
  exact h

theorem egbFixedChargeA_middle_heat_capacity_neg (w φ τ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMiddleRadius w φ τ) < 0 := by
  have h := egbCoexistenceA_middle_heat_capacity_neg (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  rw [egbFixedChargeA_heat_capacity_function, egbFixedChargeALogScale_exp] at h
  exact h

theorem egbFixedChargeAGibbsBarrier_pos (w φ τ l : ℝ) : 0 < egbFixedChargeAGibbsBarrier w φ τ l := by
  have h := egbCoexistenceA_gibbs_barrier_pos (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeALogScale_exp, egbFixedChargeA_large_radius_transfer] at h
  exact h

theorem egbFixedChargeAMiddleRadius_critical_limit (w φ : ℝ) :
    Tendsto (egbFixedChargeAMiddleRadius w φ) atBot (𝓝 (egbFixedChargeACriticalRadius w φ)) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (egbFixedChargeASmallRadius_critical_limit w φ)
    (egbFixedChargeALargeRadius_critical_limit w φ)
      (fun τ => (egbFixedChargeAMiddleRadius_bounds w φ τ).1.le)
      (fun τ => (egbFixedChargeAMiddleRadius_bounds w φ τ).2.le)

end GaloisForLFunctions.HTGeometry
