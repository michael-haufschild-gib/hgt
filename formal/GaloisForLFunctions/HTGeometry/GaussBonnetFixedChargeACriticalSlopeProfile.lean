import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorSlopeFactors

/-!
# Universal leading slope profile across the critical phase interval

At relative mean-radius displacement sin(ψ), the actual temperature slope
has leading profile C (3 sin²(ψ) - 1) / 2. Both stable phases have the
same positive coefficient C, while the mean has coefficient -C/2.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeACriticalSlopeCoefficient (w φ : ℝ) : ℝ :=
  (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (3 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 2 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ 2)

theorem egbFixedChargeACriticalSlopeCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeACriticalSlopeCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have hpi := Real.pi_pos
  unfold egbFixedChargeACriticalSlopeCoefficient
  positivity

theorem egbFixedChargeAInterior_radial_slope_critical_profile (w φ ψ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeAInteriorRadius w φ τ ψ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ * (3 * sin ψ ^ 2 - 1) / 2)) := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  have hn := ((egbFixedChargeAInteriorRadius_square_gap_critical_limit w φ ψ).pow 2).mul
    (egbFixedChargeAInterior_radial_factor_limit w φ ψ)
  have hlead := hn.div (egbFixedChargeAInterior_radial_denominator_limit w φ ψ) (by positivity)
  simp only [Pi.div_def] at hlead
  have hpress := (egbFixedChargeAPressureGap_quadratic_critical_limit w φ).mul (egbFixedChargeAInterior_pressure_slope_limit w φ ψ)
  simp only [egbFixedChargeAInterior_radial_slope_decomposition]
  have h := hlead.sub hpress
  convert h using 1
  congr 1
  unfold egbFixedChargeACriticalSlopeCoefficient egbFixedChargeAPressureGapCoefficient
  field_simp <;> ring

theorem egbFixedChargeAInterior_actual_slope_critical_profile (w φ ψ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeAInteriorRadius w φ τ ψ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ * (3 * sin ψ ^ 2 - 1) / 2)) := by
  simp only [egbFixedChargeAInterior_temperature_derivative]
  exact egbFixedChargeAInterior_radial_slope_critical_profile w φ ψ

theorem egbFixedChargeA_large_radial_slope_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeALargeRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ)) := by
  have h := egbFixedChargeAInterior_radial_slope_critical_profile w φ (Real.pi / 2)
  simp only [egbFixedChargeAInteriorRadius_large, sin_pi_div_two] at h
  convert h using 1 <;> ring

theorem egbFixedChargeA_small_radial_slope_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeASmallRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ)) := by
  have hs : sin (-Real.pi / 2) = -1 := by rw [neg_div, sin_neg, sin_pi_div_two]
  have h := egbFixedChargeAInterior_radial_slope_critical_profile w φ (-Real.pi / 2)
  simp only [egbFixedChargeAInteriorRadius_small, hs] at h
  convert h using 1 <;> ring

theorem egbFixedChargeA_mean_radial_slope_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeAMeanRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (-egbFixedChargeACriticalSlopeCoefficient w φ / 2)) := by
  have h := egbFixedChargeAInterior_radial_slope_critical_profile w φ 0
  simp only [egbFixedChargeAInteriorRadius_mean, sin_zero] at h
  convert h using 1 <;> ring

theorem egbFixedChargeA_large_actual_slope_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeALargeRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ)) := by
  simp only [egbFixedChargeA_large_thermal_slope_formula]
  exact egbFixedChargeA_large_radial_slope_quadratic_limit w φ

theorem egbFixedChargeA_small_actual_slope_quadratic_limit (w φ : ℝ) :
    Tendsto (fun τ => deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ))
      (egbFixedChargeASmallRadius w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2)
      atBot (𝓝 (egbFixedChargeACriticalSlopeCoefficient w φ)) := by
  simp only [egbFixedChargeA_small_thermal_slope_formula]
  exact egbFixedChargeA_small_radial_slope_quadratic_limit w φ

end GaloisForLFunctions.HTGeometry
