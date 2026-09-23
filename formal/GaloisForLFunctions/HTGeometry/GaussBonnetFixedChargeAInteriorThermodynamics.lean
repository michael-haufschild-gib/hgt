import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSlopeProfile

/-!
# Actual thermodynamic quantities throughout the shrinking phase interval

Intermediate radii need not be equilibria at the coexistence temperature.
Their actual temperature and entropy derivative nevertheless converge to
the critical values, and the actual heat-capacity numerator tends to 2/3.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAInterior_temperature_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeAInteriorRadius w φ τ ψ)) atBot (𝓝 (egbFixedChargeACriticalTemperature w φ)) := by
  have hr := egbFixedChargeAInteriorRadius_critical_limit w φ ψ
  have hp := egbFixedChargeAPressure_critical_limit w φ
  have hc := egbFixedChargeACriticalRadius_pos w φ
  have hpi := Real.pi_pos
  have hn := (((((tendsto_const_nhds (x := 8 * Real.pi)).mul hp).mul (hr.pow 4)).add (hr.pow 2)).sub
    (tendsto_const_nhds (x := (exp w * cos φ) ^ (2 : ℕ)))).sub (tendsto_const_nhds (x := (exp w * sin φ) ^ (2 : ℕ)))
  have hd := ((tendsto_const_nhds (x := 4 * Real.pi)).mul hr).mul
    ((hr.pow 2).add (tendsto_const_nhds (x := 2 * (exp w * sin φ) ^ (2 : ℕ))))
  have h := hn.div hd (by positivity)
  rw [← egbFixedChargeACritical_temperature_value]
  simpa only [egbTemperatureA, Pi.div_def] using h

theorem egbFixedChargeAInterior_entropy_derivative (w φ τ ψ l : ℝ) :
    deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeAInteriorRadius w φ τ ψ) =
      2 * Real.pi * egbFixedChargeAInteriorRadius w φ τ ψ +
        4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / egbFixedChargeAInteriorRadius w φ τ ψ := by
  have h := (egbEntropyA_derivative (exp w * sin φ) l (log (egbFixedChargeAInteriorRadius w φ τ ψ))).deriv
  rwa [exp_log (egbFixedChargeAInteriorRadius_pos w φ τ ψ)] at h

theorem egbFixedChargeAInterior_entropy_derivative_critical_limit (w φ ψ l : ℝ) :
    Tendsto (fun τ => deriv (egbEntropyA (exp w * sin φ) l) (egbFixedChargeAInteriorRadius w φ τ ψ))
      atBot (𝓝 (2 * Real.pi * egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have hr := egbFixedChargeAInteriorRadius_critical_limit w φ ψ
  have hc := egbFixedChargeACriticalRadius_pos w φ
  simp only [egbFixedChargeAInterior_entropy_derivative]
  have h := ((tendsto_const_nhds (x := 2 * Real.pi)).mul hr).add
    ((tendsto_const_nhds (x := 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ))).div hr hc.ne')
  simp only [Pi.div_def] at h
  have he : 2 * Real.pi * egbFixedChargeACriticalRadius w φ + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / egbFixedChargeACriticalRadius w φ =
      2 * Real.pi * egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ) := by
    rw [egbFixedChargeACritical_coupling_scaling]
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeAInterior_heat_numerator_critical_limit (w φ ψ : ℝ) :
    Tendsto (fun τ => egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ)
      (egbFixedChargeAInteriorRadius w φ τ ψ) *
        (2 * Real.pi * egbFixedChargeAInteriorRadius w φ τ ψ + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / egbFixedChargeAInteriorRadius w φ τ ψ))
      atBot (𝓝 (2 / 3 : ℝ)) := by
  have h := (egbFixedChargeAInterior_temperature_critical_limit w φ ψ).mul
    (egbFixedChargeAInterior_entropy_derivative_critical_limit w φ ψ 0)
  simp only [egbFixedChargeAInterior_entropy_derivative] at h
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hpi := Real.pi_pos
  have he : egbFixedChargeACriticalTemperature w φ *
      (2 * Real.pi * egbFixedChargeACriticalRadius w φ * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ)) = 2 / 3 := by
    unfold egbFixedChargeACriticalTemperature
    field_simp <;> ring
  rwa [he] at h

theorem egbFixedChargeAInterior_heat_capacity_formula (w φ τ ψ l : ℝ) :
    egbHeatCapacityA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ ψ) =
      egbTemperatureA (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeAInteriorRadius w φ τ ψ) *
        (2 * Real.pi * egbFixedChargeAInteriorRadius w φ τ ψ + 4 * Real.pi * (exp w * sin φ) ^ (2 : ℕ) / egbFixedChargeAInteriorRadius w φ τ ψ) /
      egbTemperatureARadialSlope (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) (egbFixedChargeAInteriorRadius w φ τ ψ) := by
  have h := egbHeatCapacityA_formula (egbFixedChargeAPressure w φ τ) (exp w * cos φ) (exp w * sin φ) l
    (log (egbFixedChargeAInteriorRadius w φ τ ψ))
  rwa [exp_log (egbFixedChargeAInteriorRadius_pos w φ τ ψ)] at h

end GaloisForLFunctions.HTGeometry
