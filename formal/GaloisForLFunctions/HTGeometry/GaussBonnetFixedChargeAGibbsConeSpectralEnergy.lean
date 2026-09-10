import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsConeFamily

/-! # Exact actual Fourier energies and prescribed positive source masses -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The actual slow Fourier energy is the prescribed slow mass times the common squared amplitude. -/
theorem egbFixedChargeAGibbsCone_slow_energy (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 * x := by
  rw [egbFixedChargeAGibbsSlowModeEnergy_reconstruction,
    egbFixedChargeAGibbsCone_collision, egbFixedChargeAGibbsCone_collision]
  ring

/-- The compensating rate power realizes an arbitrary fast mass at the chosen offset. -/
theorem egbFixedChargeAGibbsCone_fast_energy (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 * (16 : ℝ) ^ (m + 1) * y := by
  rw [egbFixedChargeAGibbsFastModeEnergy_reconstruction,
    egbFixedChargeAGibbsCone_collision, egbFixedChargeAGibbsCone_collision]
  ring

/-- Cone realization introduces no unobserved discarded Fourier sector. -/
theorem egbFixedChargeAGibbsCone_discarded_energy_zero (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsConeEnergy n k m x y) = 0 := by
  have h := egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition n 1
    (egbFixedChargeAGibbsConeEnergy n k m x y)
  rw [egbFixedChargeAGibbsCone_collision, egbFixedChargeAGibbsCone_slow_energy,
    egbFixedChargeAGibbsCone_fast_energy] at h
  simp only [pow_zero, one_mul] at h
  linarith

/-- The actual observed slow source mass is an exact positive scalar multiple of the requested mass. -/
theorem egbFixedChargeAGibbsCone_slow_mass (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionSlowSourceMass n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeScale n k m x y * x := by
  apply Subtype.ext
  change (4 / 9 : ℝ) ^ (m + 1) *
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2) * x
  rw [egbFixedChargeAGibbsCone_slow_energy]
  ring

/-- The same positive scalar simultaneously realizes the independently requested fast mass. -/
theorem egbFixedChargeAGibbsCone_fast_mass (n k m : ℕ) (x y : NNReal) :
    egbFixedChargeAGibbsCollisionFastSourceMass n m 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      egbFixedChargeAGibbsConeScale n k m x y * y := by
  apply Subtype.ext
  change (1 / 36 : ℝ) ^ (m + 1) *
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsConeEnergy n k m x y) =
      ((4 / 9 : ℝ) ^ (m + 1) * egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2) * y
  rw [egbFixedChargeAGibbsCone_fast_energy]
  have hp : (1 / 36 : ℝ) ^ (m + 1) * (16 : ℝ) ^ (m + 1) = (4 / 9 : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((1 / 36 : ℝ) ^ (m + 1) * (16 : ℝ) ^ (m + 1)) *
      egbFixedChargeAGibbsConeAmplitude n k m x y ^ 2 * y := by ring
    _ = _ := by rw [hp]

end
end GaloisForLFunctions.HTGeometry
