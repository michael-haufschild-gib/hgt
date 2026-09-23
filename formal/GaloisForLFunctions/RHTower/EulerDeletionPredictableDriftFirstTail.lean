import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingalePhysicalBridge
import GaloisForLFunctions.RHTower.EulerDeletionFirstTailWindowEnergy

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace RHTower.DeletionPredictableFirstTail

/-- The complete Báez--Duarte error energy is controlled by the exact source
Gram energy, with the unit target retained. -/
theorem fullErrorEnergy_le_two_sourceGram_add_two (N : ℕ) :
    bdMobiusFullErrorEnergy N ≤
      2 * DeletionRamarePhysical.sourceGramEnergy N + 2 := by
  rw [bdMobiusFullErrorEnergy_eq_norm_sq, ← bdTarget_sub_bdMobiusModularApproximantVec_eq]
  rw [DeletionRamarePhysical.sourceGramEnergy_eq_modular_norm_sq]
  have hnorm : ‖bdTarget - bdMobiusModularApproximantVec N‖ ≤
      1 + ‖bdMobiusModularApproximantVec N‖ := by
    calc
      _ ≤ ‖bdTarget‖ + ‖bdMobiusModularApproximantVec N‖ := norm_sub_le _ _
      _ = _ := by rw [norm_bdTarget]
  have hsq : ‖bdTarget - bdMobiusModularApproximantVec N‖ ^ (2 : ℕ) ≤
      (1 + ‖bdMobiusModularApproximantVec N‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  nlinarith [sq_nonneg (1 - ‖bdMobiusModularApproximantVec N‖)]

/-- The literal fixed-cutoff Mertens window is forced below the chronological
predictable-drift energy. -/
theorem incrementEnergy_le_twentyfour_drift_sq_add_sixty (N : ℕ) :
    DeletionFirstTail.incrementEnergy N ≤
      24 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ (2 : ℕ) + 60 := by
  have htail := DeletionFirstTail.incrementEnergy_le_six_fullErrorEnergy N
  have herror := fullErrorEnergy_le_two_sourceGram_add_two N
  have hdrift := DeletionResidueMartingalePhysical.sourceGramEnergy_le_two_drift_sq_add_four N
  nlinarith

/-- The same necessary ceiling written on the exact fixed-lower-endpoint
Möbius windows of the literal first EDQ tail. -/
theorem weighted_window_energy_le_twentyfour_drift_sq_add_sixty (N : ℕ) :
    (∑ n ∈ Finset.Ioc N (2 * N),
      ‖∑ m ∈ Finset.Ioc N n, Sieve.moebiusC m‖ ^ (2 : ℕ) /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤
      24 * ‖DeletionResidueMartingale.predictableDrift N‖ ^ (2 : ℕ) + 60 := by
  rw [← DeletionFirstTail.incrementEnergy_eq_weighted_window_energy]
  exact incrementEnergy_le_twentyfour_drift_sq_add_sixty N

end RHTower.DeletionPredictableFirstTail
