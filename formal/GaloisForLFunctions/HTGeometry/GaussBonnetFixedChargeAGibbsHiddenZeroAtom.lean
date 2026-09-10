import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullCollisionCDD
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsFullTimeDifferences
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsHiddenEntropy

/-! # A Gibbs realization of a positive pure zero-rate atom -/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The explicit hidden Gibbs landscape stores positive erased energy and no surviving energy. -/
theorem egbFixedChargeAGibbsHidden_three_sector_classification (n : ℕ) :
    0 < egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsHiddenEnergy n) ∧
    egbFixedChargeAGibbsSlowModeEnergy n 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 ∧
    egbFixedChargeAGibbsFastModeEnergy n 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 := by
  have hab := (egbFixedChargeAGibbsCollisionExcess_positive_time_zero_iff n 0 1
    (egbFixedChargeAGibbsHiddenEnergy n)).mp (egbFixedChargeAGibbsHidden_collision_erased n 0)
  have hne : egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsHiddenEnergy n) ≠ 0 := by
    intro hz
    have hu := (egbFixedChargeAGibbsCollisionExcess_zero_iff_uniform n 0 1
      (egbFixedChargeAGibbsHiddenEnergy n)).mp hz
    have he : egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsHiddenEnergy n) =
        (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := funext hu
    rw [egbFixedChargeAGibbsHidden_initial] at he
    exact egbFixedChargeACriticalHiddenProbability_nonuniform n he
  have hp := lt_of_le_of_ne (egbFixedChargeAGibbsCollisionExcess_nonneg n 0 1
    (egbFixedChargeAGibbsHiddenEnergy n)) (Ne.symm hne)
  rw [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition, hab.1, hab.2] at hp
  exact ⟨by simpa using hp, hab⟩

/-- The hidden Gibbs source is exactly a positive atom at zero, with no positive-rate support. -/
theorem egbFixedChargeAGibbsHidden_full_source_zero_atom (n : ℕ) :
    egbFixedChargeAGibbsFullCollisionHausdorffSource n 1 (egbFixedChargeAGibbsHiddenEnergy n) =
      hausdorffAtomSource (egbFixedChargeAGibbsFullCollisionErasedMass n 1 (egbFixedChargeAGibbsHiddenEnergy n))
        egbFixedChargeAGibbsCollisionZeroNode := by
  have h := egbFixedChargeAGibbsHidden_three_sector_classification n
  have ha : egbFixedChargeAGibbsFullCollisionSlowMass n 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 := by
    apply Subtype.ext
    exact h.2.1
  have hb : egbFixedChargeAGibbsFullCollisionFastMass n 1 (egbFixedChargeAGibbsHiddenEnergy n) = 0 := by
    apply Subtype.ext
    exact h.2.2
  simp only [egbFixedChargeAGibbsFullCollisionHausdorffSource, ha, hb, hausdorffAtomSource, zero_smul, add_zero]

/-- Complete one-step erasure realizes a pure flat-JT phase ray with strictly positive coefficient. -/
theorem egbFixedChargeAGibbsHidden_full_phase_flat_JT (n : ℕ) (θ : ℝ) :
    egbFixedChargeAGibbsFullCollisionCDDPhase n 1 (egbFixedChargeAGibbsHiddenEnergy n) θ =
      8 * egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsHiddenEnergy n) * Real.sinh θ := by
  have h := egbFixedChargeAGibbsHidden_three_sector_classification n
  rw [egbFixedChargeAGibbsFullCollisionCDDPhase_formula, h.2.1, h.2.2]
  ring

/-- Every initial signed difference of a hidden Gibbs history equals the same positive erased energy. -/
theorem egbFixedChargeAGibbsHidden_initial_differences_constant (n k : ℕ) :
    egbFixedChargeAGibbsFullCollisionSignedDifference n 0 k 1 (egbFixedChargeAGibbsHiddenEnergy n) =
      egbFixedChargeAGibbsDiscardedModeEnergy n 1 (egbFixedChargeAGibbsHiddenEnergy n) := by
  have h := egbFixedChargeAGibbsHidden_three_sector_classification n
  rw [egbFixedChargeAGibbsFullCollisionSignedDifference_formula, h.2.1, h.2.2]
  simp

end
end GaloisForLFunctions.HTGeometry
