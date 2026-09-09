import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAParameters
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAGibbs
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAThermalSlopes
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAEntropy

/-!
# Global and local stability with both conserved parameters fixed

Transport entire physical state functions, not merely values at endpoints.
The fixed-charge path has two distinct global Gibbs minima at every finite
parameter, and both phases have positive actual radial thermal response
and positive actual isobaric heat capacity.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeA_temperature_function (w φ τ : ℝ) :
    egbTemperatureA (egbCoexistenceAPressure (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACharge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) =
      egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) := by
  funext r
  unfold egbTemperatureA
  rw [egbFixedChargeA_pressure_transfer, egbFixedChargeA_charge_square, egbFixedChargeA_coupling_square]

theorem egbFixedChargeA_mass_function (w φ τ : ℝ) :
    egbMass (egbCoexistenceAPressure (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACharge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) =
      egbMass (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) := by
  funext r
  unfold egbMass
  rw [egbFixedChargeA_pressure_transfer, egbFixedChargeA_charge_square, egbFixedChargeA_coupling_square]

theorem egbFixedChargeA_entropy_function (w φ τ l : ℝ) :
    egbEntropyA (egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) l =
      egbEntropyA (exp w * sin φ) l := by
  funext r
  unfold egbEntropyA
  rw [egbFixedChargeA_coupling_square]

theorem egbFixedChargeA_gibbs_function (w φ τ l : ℝ) :
    egbOffShellGibbsA (egbCoexistenceAPressure (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceATemperature (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACharge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) l =
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l := by
  funext r
  unfold egbOffShellGibbsA
  rw [egbFixedChargeA_temperature_transfer, egbFixedChargeA_mass_function, egbFixedChargeA_entropy_function]

theorem egbFixedChargeA_heat_capacity_function (w φ τ l : ℝ) :
    egbHeatCapacityA (egbCoexistenceAPressure (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACharge (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) (egbCoexistenceACouplingRoot (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)) l =
      egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l := by
  funext r
  unfold egbHeatCapacityA
  rw [egbFixedChargeA_temperature_function, egbFixedChargeA_entropy_function]

theorem egbFixedChargeA_small_temperature (w φ τ : ℝ) :
    egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ) = (egbFixedChargeATemperature w φ τ) := by
  have h := egbCoexistenceA_small_temperature (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeA_small_radius_transfer,
    egbFixedChargeA_temperature_transfer] at h
  exact h

theorem egbFixedChargeA_large_temperature (w φ τ : ℝ) :
    egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ) = (egbFixedChargeATemperature w φ τ) := by
  have h := egbCoexistenceA_large_temperature (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeA_large_radius_transfer,
    egbFixedChargeA_temperature_transfer] at h
  exact h

theorem egbFixedChargeA_equal_gibbs (w φ τ l : ℝ) :
    egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) =
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) := by
  have h := egbCoexistenceA_equal_gibbs (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeA_small_radius_transfer, egbFixedChargeA_large_radius_transfer] at h
  exact h

theorem egbFixedChargeA_global_minimum (w φ τ l x : ℝ) :
    egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) ≤
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (exp x) := by
  have h := egbCoexistenceA_global_minimum (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l x
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeA_large_radius_transfer] at h
  exact h

theorem egbFixedChargeA_global_minimizers_iff (w φ τ l x : ℝ) :
    egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (exp x) =
      egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) ↔
    exp x = egbFixedChargeASmallRadius w φ τ ∨ exp x = egbFixedChargeALargeRadius w φ τ := by
  have h := egbCoexistenceA_global_minimizers_iff (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l x
  rw [egbFixedChargeA_gibbs_function, egbFixedChargeA_small_radius_transfer, egbFixedChargeA_large_radius_transfer] at h
  exact h

theorem egbFixedChargeA_small_thermal_slope_pos (w φ τ : ℝ) :
    0 < deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeASmallRadius w φ τ) := by
  have h := egbCoexistenceA_small_thermal_slope_pos (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeA_small_radius_transfer] at h
  exact h

theorem egbFixedChargeA_small_heat_capacity_pos (w φ τ l : ℝ) :
    0 < egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeASmallRadius w φ τ) := by
  have h := egbCoexistenceA_small_heat_capacity_pos (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  rw [egbFixedChargeA_heat_capacity_function, egbFixedChargeA_small_radius_transfer] at h
  exact h

theorem egbFixedChargeA_large_thermal_slope_pos (w φ τ : ℝ) :
    0 < deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeALargeRadius w φ τ) := by
  have h := egbCoexistenceA_large_thermal_slope_pos (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ)
  rw [egbFixedChargeA_temperature_function, egbFixedChargeA_large_radius_transfer] at h
  exact h

theorem egbFixedChargeA_large_heat_capacity_pos (w φ τ l : ℝ) :
    0 < egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ) := by
  have h := egbCoexistenceA_large_heat_capacity_pos (egbFixedChargeALogScale w φ τ) τ (egbFixedChargeAAngle τ φ) l
  rw [egbFixedChargeA_heat_capacity_function, egbFixedChargeA_large_radius_transfer] at h
  exact h

end GaloisForLFunctions.HTGeometry
