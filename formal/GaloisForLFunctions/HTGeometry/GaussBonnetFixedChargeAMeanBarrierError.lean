import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitCriticalLimit
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitBounds

/-!
# Quantitative relative error of the arithmetic-mean barrier estimate

The relative error is quadratic in phase asymmetry and linear in either
physical gap to criticality. Dividing it by the squared moving peak
coordinate gives the parameter-independent limit two.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanBarrier_relative_error_formula (w φ τ l : ℝ) :
    1 - egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbFixedChargeAGibbsBarrier w φ τ l =
      egbFixedChargeAMeanGibbsDeficit w φ τ l / egbFixedChargeAGibbsBarrier w φ τ l := by
  have hB := egbFixedChargeAGibbsBarrier_pos w φ τ l
  rw [egbFixedChargeAMeanGibbsDeficit_gap_difference]
  field_simp

theorem egbFixedChargeAMeanBarrier_relative_error_quadratic_limit (w φ l : ℝ) :
    Tendsto (fun τ => (1 - egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbFixedChargeAGibbsBarrier w φ τ l) /
      egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2)) := by
  simp only [egbFixedChargeAMeanBarrier_relative_error_formula]
  exact egbFixedChargeAMeanGibbsDeficit_barrier_quadratic_limit w φ l l

theorem egbFixedChargeAMeanBarrier_relative_error_temperature_limit (w φ l : ℝ) :
    Tendsto (fun τ => (1 - egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbFixedChargeAGibbsBarrier w φ τ l) /
      (egbFixedChargeACriticalTemperature w φ - egbFixedChargeATemperature w φ τ))
      atBot (𝓝 ((2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2) / egbFixedChargeATemperatureGapCoefficient w φ)) := by
  have h := (egbFixedChargeAMeanBarrier_relative_error_quadratic_limit w φ l).div
    (egbFixedChargeATemperatureGap_quadratic_critical_limit w φ) (egbFixedChargeATemperatureGapCoefficient_pos w φ).ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMeanBarrier_relative_error_pressure_limit (w φ l : ℝ) :
    Tendsto (fun τ => (1 - egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbFixedChargeAGibbsBarrier w φ τ l) /
      (egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ))
      atBot (𝓝 ((2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2) / egbFixedChargeAPressureGapCoefficient w φ)) := by
  have h := (egbFixedChargeAMeanBarrier_relative_error_quadratic_limit w φ l).div
    (egbFixedChargeAPressureGap_quadratic_critical_limit w φ) (egbFixedChargeAPressureGapCoefficient_pos w φ).ne'
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleGapCoordinate_linear_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleGapCoordinate τ φ / egbCoexistenceASymmetricRatio τ)
      atBot (𝓝 (egbFixedChargeAMiddleMeanCorrection φ)) := by
  convert egbFixedChargeAMiddleQuadraticShift_critical_limit φ using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [← egbFixedChargeAMiddleQuadraticShift_gap]
  field_simp

theorem egbFixedChargeAMeanBarrier_relative_error_peak_coordinate_limit (w φ l : ℝ) :
    Tendsto (fun τ => (1 - egbFixedChargeAInteriorGibbsGap w φ τ l 0 / egbFixedChargeAGibbsBarrier w φ τ l) /
      egbFixedChargeAMiddleGapCoordinate τ φ ^ 2) atBot (𝓝 (2 : ℝ)) := by
  have hc := egbFixedChargeAMiddleMeanCorrection_neg φ
  have h := (egbFixedChargeAMeanBarrier_relative_error_quadratic_limit w φ l).div
    ((egbFixedChargeAMiddleGapCoordinate_linear_limit φ).pow 2) (pow_ne_zero 2 hc.ne)
  have he : (2 * egbFixedChargeAMiddleMeanCorrection φ ^ 2) / egbFixedChargeAMiddleMeanCorrection φ ^ 2 = 2 := by
    field_simp [hc.ne]
  rw [he] at h
  simp only [Pi.div_def] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

end GaloisForLFunctions.HTGeometry
