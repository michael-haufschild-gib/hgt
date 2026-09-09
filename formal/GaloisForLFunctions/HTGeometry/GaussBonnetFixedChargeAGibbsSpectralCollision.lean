import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalSharpRelaxation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every normalized Gibbs population has the same invariant uniform mean. -/
theorem egbFixedChargeAGibbsPopulation_uniform_mean (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalRealMean n (egbFixedChargeAGibbsMarkovPopulation n m β E) =
      ((2 : ℝ) ^ (n + 3))⁻¹ := by
  rw [egbFixedChargeACriticalRealMean, egbFixedChargeAGibbsMarkovPopulation_mass, mul_one]

/-- The corpus collision excess is precisely centered squared norm for Gibbs populations. -/
theorem egbFixedChargeAGibbsPopulation_centered_energy (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredEnergy n (egbFixedChargeAGibbsMarkovPopulation n m β E) =
      egbFixedChargeAGibbsCollisionExcess n m β E := by
  simp only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeACriticalCenteredProfile,
    egbFixedChargeAGibbsPopulation_uniform_mean]
  rfl

/-- Spectral structure contracts Gibbs collision excess by four ninths at each transition. -/
theorem egbFixedChargeAGibbsCollisionExcess_spectral_step (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n (m + 1) β E ≤
      (4 / 9) * egbFixedChargeAGibbsCollisionExcess n m β E := by
  rw [← egbFixedChargeAGibbsPopulation_centered_energy n (m + 1) β E,
    ← egbFixedChargeAGibbsPopulation_centered_energy n m β E]
  have ha := egbFixedChargeAGibbsMarkovPopulation_add n 1 m β E
  rw [Nat.add_comm 1 m] at ha
  rw [ha]
  exact egbFixedChargeACriticalCenteredEnergy_step n _

/-- Every Gibbs population has an all-time spectral bound on collision excess. -/
theorem egbFixedChargeAGibbsCollisionExcess_spectral_bound (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m β E ≤
      (4 / 9 : ℝ) ^ m * egbFixedChargeAGibbsCollisionExcess n 0 β E := by
  rw [← egbFixedChargeAGibbsPopulation_centered_energy n m β E,
    ← egbFixedChargeAGibbsPopulation_centered_energy n 0 β E,
    egbFixedChargeAGibbsMarkovPopulation_zero]
  exact egbFixedChargeACriticalCenteredEnergy_geometric n m
    (_root_.HTGeometry.finiteGibbsStateWeight β E)

end
end GaloisForLFunctions.HTGeometry
