import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorRadius
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalARadialFactorization

/-!
# Critical limits of the exact radial-slope factors throughout the phase interval
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInterior_radial_factor_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => 8 * Real.pi * egbFixedChargeACriticalPressure w φ * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 +
      2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ)
      atBot (𝓝 ((1 - 2 * egbFixedChargeACriticalCouplingWeight φ) / 2)) := by
  have h := ((tendsto_const_nhds (x := 8 * Real.pi * egbFixedChargeACriticalPressure w φ)).mul
    ((egbFixedChargeAInteriorRadius_critical_limit w φ ψ).pow 2)).add
      (tendsto_const_nhds (x := 2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ))
  rwa [egbFixedChargeACritical_radial_factor_at_critical] at h

theorem egbFixedChargeAInterior_radial_denominator_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => 4 * Real.pi * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 *
      (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2)
      atBot (𝓝 (4 * Real.pi * egbFixedChargeACriticalRadius w φ ^ 6 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ 2)) := by
  have hr := egbFixedChargeAInteriorRadius_critical_limit w φ ψ
  have h := ((tendsto_const_nhds (x := 4 * Real.pi)).mul (hr.pow 2)).mul
    (((hr.pow 2).add (tendsto_const_nhds (x := 2 * (exp w * sin φ) ^ 2))).pow 2)
  convert h using 1
  rw [egbFixedChargeACritical_coupling_scaling]
  ring

theorem egbFixedChargeAInterior_pressure_slope_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => 2 * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 *
      (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 6 * (exp w * sin φ) ^ 2) /
        (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2)
      atBot (𝓝 (2 * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ) / (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) ^ 2)) := by
  have hr := egbFixedChargeAInteriorRadius_critical_limit w φ ψ
  have hc := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hn := ((tendsto_const_nhds (x := (2 : ℝ))).mul (hr.pow 2)).mul
    ((hr.pow 2).add (tendsto_const_nhds (x := 6 * (exp w * sin φ) ^ 2)))
  have hd := ((hr.pow 2).add (tendsto_const_nhds (x := 2 * (exp w * sin φ) ^ 2))).pow 2
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  convert h using 1
  rw [egbFixedChargeACritical_coupling_scaling]
  field_simp <;> ring

theorem egbFixedChargeAInterior_radial_slope_decomposition (w φ τ ψ : ℝ) :
    egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeAInteriorRadius w φ τ ψ) /
      egbCoexistenceASymmetricRatio τ ^ 2 =
      ((egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 - egbFixedChargeACriticalRadius w φ ^ 2) / egbCoexistenceASymmetricRatio τ) ^ 2 *
        (8 * Real.pi * egbFixedChargeACriticalPressure w φ * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 +
          2 * egbFixedChargeACriticalCouplingWeight φ * egbFixedChargeACriticalWeight φ) /
        (4 * Real.pi * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 *
          (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2) -
      ((egbFixedChargeACriticalPressure w φ - egbFixedChargeAPressure w φ τ) / egbCoexistenceASymmetricRatio τ ^ 2) *
        (2 * egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 * (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 6 * (exp w * sin φ) ^ 2) /
          (egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 2 * (exp w * sin φ) ^ 2) ^ 2) := by
  have hr := egbFixedChargeAInteriorRadius_pos w φ τ ψ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hpi := Real.pi_pos
  have hD : 0 < egbFixedChargeAInteriorRadius w φ τ ψ ^ 2 + 2 * (exp w * sin φ) ^ 2 := by positivity
  have h := egbFixedChargeA_radial_slope_pressure_decomposition (egbFixedChargeAPressure w φ τ) w φ (log (egbFixedChargeAInteriorRadius w φ τ ψ))
  rw [exp_log hr] at h
  rw [h]
  field_simp <;> ring

theorem egbFixedChargeAInterior_temperature_derivative (w φ τ ψ : ℝ) :
    deriv (egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)) (egbFixedChargeAInteriorRadius w φ τ ψ) =
      egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeAInteriorRadius w φ τ ψ) := by
  have h := (egbTemperatureA_hasDerivAt (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
    (log (egbFixedChargeAInteriorRadius w φ τ ψ))).deriv
  rwa [exp_log (egbFixedChargeAInteriorRadius_pos w φ τ ψ)] at h

end GaloisForLFunctions.HTGeometry
