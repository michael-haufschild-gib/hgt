import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalContraction
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs

/-!
# Slow-mode elimination and erasure-visible relaxation

Chattopadhyay, arXiv:2608.16254, relates relaxation speed to the initial
projection onto slow Liouvillian modes. The corpus's exact thermal energy law
identifies that projection with coherence. Pinching eliminates the slow sector
while preserving the entire erasure-population trajectory: faster full-state
relaxation need not change an observable that cannot see the slow sector.
-/

noncomputable section
open Matrix Filter
open scoped Matrix Topology
namespace GaloisForLFunctions.HTGeometry.Thermofield
open SchafferExl

/-- Removing the known exponential decay reveals the slow projection exactly. -/
theorem thermalEnergy_rescaled (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    spinThermalEnergy u ((spinThermalChannel a u t).map ρ) / spinDecayMass a t =
      spinDecayMass a t * spinThermalPopulationEnergy u ρ + spinThermalCoherenceEnergy ρ := by
  rw [spinThermalEnergy_channel]
  field_simp [(spinDecayMass_pos a t).ne']

/-- Positive damping makes the rescaled error converge to the coherence energy. -/
theorem thermalEnergy_rescaled_tendsto (s u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t => spinThermalEnergy u ((spinThermalChannel (Real.exp s) u t).map ρ) /
      spinDecayMass (Real.exp s) t) atTop (𝓝 (spinThermalCoherenceEnergy ρ)) := by
  simp_rw [thermalEnergy_rescaled]
  simpa only [zero_mul, zero_add] using
    ((spinDecayMass_tendsto_zero s).mul_const (spinThermalPopulationEnergy u ρ)).add_const
      (spinThermalCoherenceEnergy ρ)

/-- The slow sector vanishes exactly when both coherences vanish. -/
theorem thermalCoherenceEnergy_eq_zero_iff (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinThermalCoherenceEnergy ρ = 0 ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0 := by
  rw [spinThermalCoherenceEnergy, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff, norm_eq_zero, norm_eq_zero]

/-- Faster full-state relaxation is equivalent to absence of coherence. -/
theorem thermal_fast_relaxation_iff (s u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t => spinThermalEnergy u ((spinThermalChannel (Real.exp s) u t).map ρ) /
      spinDecayMass (Real.exp s) t) atTop (𝓝 0) ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0 := by
  rw [← thermalCoherenceEnergy_eq_zero_iff]
  constructor
  · intro h
    exact tendsto_nhds_unique (thermalEnergy_rescaled_tendsto s u ρ) h
  · intro h
    simpa only [h] using thermalEnergy_rescaled_tendsto s u ρ

/-- The corpus's actual measurement channel removes every slow thermal mode. -/
theorem thermal_pinching_fast (s u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t => spinThermalEnergy u
      ((spinThermalChannel (Real.exp s) u t).map (spinZPinch ρ)) /
      spinDecayMass (Real.exp s) t) atTop (𝓝 0) := by
  apply (thermal_fast_relaxation_iff s u (spinZPinch ρ)).mpr
  simp [spinZPinch_entries]

/-- The erasure population sees only the fast population coefficient. -/
theorem thermal_erasure_population (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    (spinThermalChannel a u t).map ρ 0 0 -
      (spinBathUpper u : ℂ) * Matrix.trace ρ =
      (spinDecayMass a t : ℂ) * (ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ) := by
  simp [spinThermalChannel_entries]
  ring

/-- Removing the slow sector leaves the entire erasure-population trajectory unchanged. -/
theorem thermal_erasure_population_pinching (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    (spinThermalChannel a u t).map (spinZPinch ρ) 0 0 =
      (spinThermalChannel a u t).map ρ 0 0 := by
  simp [spinThermalChannel_entries, spinZPinch_entries, Matrix.trace, Fin.sum_univ_two]

end GaloisForLFunctions.HTGeometry.Thermofield
