import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTunableFamily

/-! # The actual retained Fourier energies of the tunable Gibbs family -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Two observed collision values identify the exact slow Fourier energy of the constructed Gibbs law. -/
theorem egbFixedChargeAGibbsTunable_slow_energy (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableAmplitude n k m t ^ (2 : ℕ) := by
  rw [egbFixedChargeAGibbsSlowModeEnergy_reconstruction,
    egbFixedChargeAGibbsTunable_collision, egbFixedChargeAGibbsTunable_collision]
  ring

/-- The fast Fourier energy contains precisely the compensating rate power and the squared ratio parameter. -/
theorem egbFixedChargeAGibbsTunable_fast_energy (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      egbFixedChargeAGibbsTunableAmplitude n k m t ^ (2 : ℕ) * (16 : ℝ) ^ (m + 1) * t ^ (2 : ℕ) := by
  rw [egbFixedChargeAGibbsFastModeEnergy_reconstruction,
    egbFixedChargeAGibbsTunable_collision, egbFixedChargeAGibbsTunable_collision]
  ring

/-- The constructed Gibbs law carries no discarded Fourier energy at all. -/
theorem egbFixedChargeAGibbsTunable_discarded_energy_zero (n k m : ℕ) (t : ℝ) :
    egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t) = 0 := by
  have h := egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition n 1
    (egbFixedChargeAGibbsTunableEnergy n k m t)
  rw [egbFixedChargeAGibbsTunable_collision, egbFixedChargeAGibbsTunable_slow_energy,
    egbFixedChargeAGibbsTunable_fast_energy] at h
  simp only [pow_zero, one_mul] at h
  nlinarith

/-- The observed slow source mass is always strictly positive. -/
theorem egbFixedChargeAGibbsTunable_slow_mass_pos (n k m : ℕ) (t : ℝ) :
    0 < (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1
      (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) := by
  change 0 < (4 / 9 : ℝ) ^ (m + 1) *
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t)
  rw [egbFixedChargeAGibbsTunable_slow_energy]
  exact mul_pos (pow_pos (by norm_num) _) (sq_pos_of_pos (egbFixedChargeAGibbsTunableAmplitude_pos n k m t))

/-- At the selected observation offset the actual fast-to-slow mass ratio is exactly t squared. -/
theorem egbFixedChargeAGibbsTunable_source_mass_ratio (n k m : ℕ) (t : ℝ) :
    (egbFixedChargeAGibbsCollisionFastSourceMass n m 1 (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) =
      (egbFixedChargeAGibbsCollisionSlowSourceMass n m 1
        (egbFixedChargeAGibbsTunableEnergy n k m t) : ℝ) * t ^ (2 : ℕ) := by
  change (1 / 36 : ℝ) ^ (m + 1) *
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t) =
      ((4 / 9 : ℝ) ^ (m + 1) *
        egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsTunableEnergy n k m t)) * t ^ (2 : ℕ)
  rw [egbFixedChargeAGibbsTunable_fast_energy, egbFixedChargeAGibbsTunable_slow_energy]
  have hp : (1 / 36 : ℝ) ^ (m + 1) * (16 : ℝ) ^ (m + 1) = (4 / 9 : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((1 / 36 : ℝ) ^ (m + 1) * (16 : ℝ) ^ (m + 1)) *
      egbFixedChargeAGibbsTunableAmplitude n k m t ^ (2 : ℕ) * t ^ (2 : ℕ) := by ring
    _ = _ := by rw [hp]

end
end GaloisForLFunctions.HTGeometry
