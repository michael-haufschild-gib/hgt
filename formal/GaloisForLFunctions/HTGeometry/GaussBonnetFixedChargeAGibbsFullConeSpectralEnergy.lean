import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullConeFamily
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionHausdorffSource

/-! # Exact actual realization of all three full-history source masses -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The prescribed slow mass is the actual slow Fourier energy up to the common positive scale. -/
theorem egbFixedChargeAGibbsFullCone_slow_energy (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * A := by
  rw [egbFixedChargeAGibbsSlowModeEnergy_reconstruction,
    egbFixedChargeAGibbsFullCone_collision, egbFixedChargeAGibbsFullCone_collision]
  norm_num
  ring

/-- The prescribed fast mass independently realizes the actual fast Fourier energy. -/
theorem egbFixedChargeAGibbsFullCone_fast_energy (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * B := by
  rw [egbFixedChargeAGibbsFastModeEnergy_reconstruction,
    egbFixedChargeAGibbsFullCone_collision, egbFixedChargeAGibbsFullCone_collision]
  norm_num
  ring

/-- The third prescribed mass is exactly the actual energy erased by the first transition. -/
theorem egbFixedChargeAGibbsFullCone_discarded_energy (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * R := by
  have h := egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition n 1
    (egbFixedChargeAGibbsFullConeEnergy n k R A B)
  rw [egbFixedChargeAGibbsFullCone_collision, egbFixedChargeAGibbsFullCone_slow_energy,
    egbFixedChargeAGibbsFullCone_fast_energy] at h
  simp only [pow_zero, one_mul] at h
  linarith

/-- The full erased source mass is an exact positive scaling of the requested endpoint mass. -/
theorem egbFixedChargeAGibbsFullCone_erased_mass (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFullCollisionErasedMass n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeScale n k R A B * R := by
  apply Subtype.ext
  change egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
    egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * (R : ℝ)
  exact egbFixedChargeAGibbsFullCone_discarded_energy n k R A B

/-- The full slow source mass has the same positive scaling. -/
theorem egbFixedChargeAGibbsFullCone_slow_mass (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFullCollisionSlowMass n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeScale n k R A B * A := by
  apply Subtype.ext
  change egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
    egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * (A : ℝ)
  exact egbFixedChargeAGibbsFullCone_slow_energy n k R A B

/-- The full fast source mass completes the simultaneous realization of the requested triple. -/
theorem egbFixedChargeAGibbsFullCone_fast_mass (n k : ℕ) (R A B : NNReal) :
    egbFixedChargeAGibbsFullCollisionFastMass n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
      egbFixedChargeAGibbsFullConeScale n k R A B * B := by
  apply Subtype.ext
  change egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsFullConeEnergy n k R A B) =
    egbFixedChargeAGibbsFullConeAmplitude n k R A B ^ 2 * (B : ℝ)
  exact egbFixedChargeAGibbsFullCone_fast_energy n k R A B

end
end GaloisForLFunctions.HTGeometry
