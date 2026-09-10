import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsDiscardedModeEnergy
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsCollisionIdentification

/-!
# The complete three-rate collision history

The zero-rate atom records information destroyed at the first transition.
Together with the two surviving atoms it determines the entire history,
including time zero, from only three scalar observations.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The entire collision history is a positive mixture at rates zero, four ninths, and one thirty-sixth. -/
theorem egbFixedChargeAGibbsCollisionExcess_full_time_three_rate (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E =
      (0 : ℝ) ^ m * egbFixedChargeAGibbsDiscardedModeEnergy n β E +
      (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (1 / 36 : ℝ) ^ m * egbFixedChargeAGibbsFastModeEnergy n β E := by
  cases m with
  | zero => simpa using egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition n β E
  | succ m =>
      rw [egbFixedChargeAGibbsCollisionExcess_two_rate n m β E]
      simp

/-- Three initial collision observations recover exactly the energy erased in the first transition. -/
theorem egbFixedChargeAGibbsDiscardedModeEnergy_reconstruction (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsDiscardedModeEnergy n β E =
      egbFixedChargeAGibbsCollisionExcess n 0 β E -
      (153 / 4 : ℝ) * egbFixedChargeAGibbsCollisionExcess n 1 β E +
      81 * egbFixedChargeAGibbsCollisionExcess n 2 β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition,
    egbFixedChargeAGibbsCollisionExcess_two_rate n 0 β E,
    egbFixedChargeAGibbsCollisionExcess_two_rate n 1 β E]
  ring

/-- Equality of the full history is equivalent to equality of its first three collision observations. -/
theorem egbFixedChargeAGibbsCollisionExcess_full_history_iff_three_values (n : ℕ) (β γ : ℝ)
    (E F : Fin (2 ^ (n + 3)) → ℝ) :
    (∀ m : ℕ, egbFixedChargeAGibbsCollisionExcess n m β E =
      egbFixedChargeAGibbsCollisionExcess n m γ F) ↔
      egbFixedChargeAGibbsCollisionExcess n 0 β E = egbFixedChargeAGibbsCollisionExcess n 0 γ F ∧
      egbFixedChargeAGibbsCollisionExcess n 1 β E = egbFixedChargeAGibbsCollisionExcess n 1 γ F ∧
      egbFixedChargeAGibbsCollisionExcess n 2 β E = egbFixedChargeAGibbsCollisionExcess n 2 γ F := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ m
    cases m with
    | zero => exact h0
    | succ m => exact (egbFixedChargeAGibbsCollisionExcess_history_iff_two_values n β γ E F).mpr ⟨h1, h2⟩ m

/-- Initial equilibrium requires all three spectral sectors to vanish, including the erased one. -/
theorem egbFixedChargeAGibbsCollisionExcess_initial_zero_iff_three_energies (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n 0 β E = 0 ↔
      egbFixedChargeAGibbsDiscardedModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsSlowModeEnergy n β E = 0 ∧
      egbFixedChargeAGibbsFastModeEnergy n β E = 0 := by
  rw [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition]
  have hR := egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E
  have hA := egbFixedChargeAGibbsSlowModeEnergy_nonneg n β E
  have hB := egbFixedChargeAGibbsFastModeEnergy_nonneg n β E
  constructor
  · intro h
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hr, ha, hb⟩
    rw [hr, ha, hb]
    ring

/-- The first collision loss splits into complete erasure and partial loss in the two surviving sectors. -/
theorem egbFixedChargeAGibbsCollisionExcess_first_step_loss (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n 0 β E - egbFixedChargeAGibbsCollisionExcess n 1 β E =
      egbFixedChargeAGibbsDiscardedModeEnergy n β E +
      (5 / 9 : ℝ) * egbFixedChargeAGibbsSlowModeEnergy n β E +
      (35 / 36 : ℝ) * egbFixedChargeAGibbsFastModeEnergy n β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition,
    egbFixedChargeAGibbsCollisionExcess_two_rate n 0 β E]
  ring

end
end GaloisForLFunctions.HTGeometry
