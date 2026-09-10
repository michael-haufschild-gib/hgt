import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsTwoRateCollision
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQFTParseval

/-!
# The Fourier energy erased in the first thermal transition

Parseval partitions initial collision excess into three nonnegative sectors:
erased modes, surviving slow modes, and surviving fast modes.
-/
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Fourier energy outside the five modes retained by the thermal transition. -/
def egbFixedChargeAGibbsDiscardedModeEnergy (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  ∑ j ∈ ((Finset.univ : Finset (Fin 5)).image (egbFixedChargeAFiveFourierModes n))ᶜ,
    ‖egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight β E i : ℂ)) j‖ ^ 2

/-- The energy discarded in the first transition is nonnegative for every Gibbs input. -/
theorem egbFixedChargeAGibbsDiscardedModeEnergy_nonneg (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 ≤ egbFixedChargeAGibbsDiscardedModeEnergy n β E := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem retained_energy_sum (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ k : Fin 5, ‖egbFixedChargeAGibbsFourierMoment n β E k‖ ^ 2) =
      ((2 : ℝ) ^ (n + 3))⁻¹ + egbFixedChargeAGibbsSlowModeEnergy n β E +
        egbFixedChargeAGibbsFastModeEnergy n β E := by
  simp [Fin.sum_univ_succ]
  rw [egbFixedChargeAGibbsFourierMoment_zero_sq_norm]
  unfold egbFixedChargeAGibbsSlowModeEnergy egbFixedChargeAGibbsFastModeEnergy
  ring

/-- Initial collision excess splits exactly into erased, slow, and fast Fourier energy. -/
theorem egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n 0 β E =
      egbFixedChargeAGibbsDiscardedModeEnergy n β E +
        egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E := by
  classical
  let S : Finset (Fin (2 ^ (n + 3))) :=
    (Finset.univ : Finset (Fin 5)).image (egbFixedChargeAFiveFourierModes n)
  let f : Fin (2 ^ (n + 3)) → ℝ := fun j =>
    ‖egbFixedChargeACriticalFourierCoordinates n
      (fun i => (_root_.HTGeometry.finiteGibbsStateWeight β E i : ℂ)) j‖ ^ 2
  have hp := Finset.sum_compl_add_sum S f
  have hs : (∑ j ∈ S, f j) =
      ∑ k : Fin 5, ‖egbFixedChargeAGibbsFourierMoment n β E k‖ ^ 2 := by
    dsimp [S]
    rw [Finset.sum_image (egbFixedChargeAFiveFourierModes_injective n).injOn]
    rfl
  rw [hs, retained_energy_sum] at hp
  have hf : (∑ j, f j) = ∑ i, (_root_.HTGeometry.finiteGibbsStateWeight β E i) ^ 2 := by
    dsimp [f]
    rw [egbFixedChargeACriticalFourierCoordinates_parseval]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hf] at hp
  change egbFixedChargeAGibbsDiscardedModeEnergy n β E +
    (((2 : ℝ) ^ (n + 3))⁻¹ + egbFixedChargeAGibbsSlowModeEnergy n β E +
      egbFixedChargeAGibbsFastModeEnergy n β E) = _ at hp
  rw [egbFixedChargeAGibbsCollisionExcess_identity, egbFixedChargeAGibbsMarkovPopulation_zero]
  linarith

/-- The surviving slow and fast energies never exceed the initial collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_initial_retained_bound (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsSlowModeEnergy n β E + egbFixedChargeAGibbsFastModeEnergy n β E ≤
      egbFixedChargeAGibbsCollisionExcess n 0 β E := by
  rw [egbFixedChargeAGibbsCollisionExcess_initial_spectral_partition]
  linarith [egbFixedChargeAGibbsDiscardedModeEnergy_nonneg n β E]

end
end GaloisForLFunctions.HTGeometry
