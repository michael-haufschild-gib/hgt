import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalGibbs

/-!
# Exact slow-mode elimination in the thermal qubit channel

Chattopadhyay, arXiv:2608.16254, relates relaxation speed to the initial
projection onto slow Liouvillian modes. In the constructed thermal qubit
channel, the off-diagonal sector is precisely the slow sector. Its elimination
is characterized by an exact rescaled limit, with no remainder assumption.
-/

noncomputable section
open Matrix Filter
open scoped Matrix ComplexConjugate Topology BigOperators
namespace GaloisForLFunctions.HTGeometry.Thermofield
open SchafferExl

/-- Squared Hilbert--Schmidt deviation from the stationary trace-scaled bath. -/
def thermalDeviationSq (a u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) : ℝ :=
  ∑ i, ∑ j, ‖(spinThermalChannel a u t).map ρ i j -
    ((Matrix.trace ρ) • spinBathDensity u) i j‖^2

/-- Coherence energy in the two slow modes. -/
def thermalSlowEnergy (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖ρ 0 1‖^2 + ‖ρ 1 0‖^2

/-- Population energy in the faster modes. -/
def thermalFastEnergy (u : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ‖^2 +
    ‖ρ 1 1 - (spinBathLower u : ℂ) * Matrix.trace ρ‖^2

private theorem thermalDeviation_entries (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    (spinThermalChannel a u t).map ρ - (Matrix.trace ρ) • spinBathDensity u =
      !![(spinDecayMass a t : ℂ) * (ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ),
        spinDecayFactor a t * ρ 0 1;
        conj (spinDecayFactor a t) * ρ 1 0,
        (spinDecayMass a t : ℂ) * (ρ 1 1 - (spinBathLower u : ℂ) * Matrix.trace ρ)] := by
  rw [spinThermalChannel_entries, spinBathDensity_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

/-- Exact two-rate decomposition of the actual channel's squared error. -/
theorem thermalDeviationSq_two_rate (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    thermalDeviationSq a u ρ t = spinDecayMass a t ^ 2 * thermalFastEnergy u ρ +
      spinDecayMass a t * thermalSlowEnergy ρ := by
  change (∑ i, ∑ j, ‖((spinThermalChannel a u t).map ρ -
    (Matrix.trace ρ) • spinBathDensity u) i j‖^2) = _
  rw [thermalDeviation_entries]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, RCLike.norm_conj, spinDecayFactor_norm_sq]
  unfold thermalFastEnergy thermalSlowEnergy
  ring

/-- Removing the known exponential decay reveals the slow projection exactly. -/
theorem thermalDeviationSq_rescaled (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    thermalDeviationSq a u ρ t / spinDecayMass a t =
      spinDecayMass a t * thermalFastEnergy u ρ + thermalSlowEnergy ρ := by
  rw [thermalDeviationSq_two_rate]
  field_simp [(spinDecayMass_pos a t).ne']

/-- Positive damping makes the rescaled error converge to the coherence energy. -/
theorem thermalDeviationSq_rescaled_tendsto (s u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t => thermalDeviationSq (Real.exp s) u ρ t /
      spinDecayMass (Real.exp s) t) atTop (𝓝 (thermalSlowEnergy ρ)) := by
  simp_rw [thermalDeviationSq_rescaled]
  simpa only [zero_mul, zero_add] using
    ((spinDecayMass_tendsto_zero s).mul_const (thermalFastEnergy u ρ)).add_const
      (thermalSlowEnergy ρ)

/-- The slow sector vanishes exactly when both coherences vanish. -/
theorem thermalSlowEnergy_eq_zero_iff (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    thermalSlowEnergy ρ = 0 ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0 := by
  unfold thermalSlowEnergy
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),
    sq_eq_zero_iff, sq_eq_zero_iff, norm_eq_zero, norm_eq_zero]

/-- Exact strong-Mpemba criterion for this channel: faster decay is equivalent to no coherence. -/
theorem thermal_fast_relaxation_iff (s u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t => thermalDeviationSq (Real.exp s) u ρ t /
      spinDecayMass (Real.exp s) t) atTop (𝓝 0) ↔ ρ 0 1 = 0 ∧ ρ 1 0 = 0 := by
  rw [← thermalSlowEnergy_eq_zero_iff]
  constructor
  · intro h
    exact tendsto_nhds_unique (thermalDeviationSq_rescaled_tendsto s u ρ) h
  · intro h
    simpa only [h] using thermalDeviationSq_rescaled_tendsto s u ρ

/-- The erasure population sees only the fast population coefficient. -/
theorem thermal_erasure_population (a u : ℝ)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (t : NNReal) :
    (spinThermalChannel a u t).map ρ 0 0 -
      (spinBathUpper u : ℂ) * Matrix.trace ρ =
      (spinDecayMass a t : ℂ) * (ρ 0 0 - (spinBathUpper u : ℂ) * Matrix.trace ρ) := by
  rw [spinThermalChannel_entries]
  simp only [Matrix.cons_val_zero]
  ring

end GaloisForLFunctions.HTGeometry.Thermofield
