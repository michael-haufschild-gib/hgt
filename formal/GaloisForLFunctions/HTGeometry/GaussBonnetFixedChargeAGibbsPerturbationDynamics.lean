import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsPerturbationRealization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized centered perturbation evolves through the original real Markov action. -/
theorem egbFixedChargeAGibbsPerturbation_evolution (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsPerturbationEnergy n f) =
      fun i => ((2 : ℝ) ^ (n + 3))⁻¹ +
        (egbFixedChargeAGibbsPerturbationScale n f / (2 : ℝ) ^ (n + 3)) *
          (egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal
            (egbFixedChargeACriticalCenteredProfile n f) i := by
  unfold egbFixedChargeAGibbsMarkovPopulation
  rw [egbFixedChargeAGibbsPerturbation_realization]
  have hp : egbFixedChargeAGibbsPerturbationProbability n f = fun i =>
      ((2 : ℝ) ^ (n + 3))⁻¹ + (egbFixedChargeAGibbsPerturbationScale n f / (2 : ℝ) ^ (n + 3)) *
        egbFixedChargeACriticalCenteredProfile n f i := by
    funext i
    unfold egbFixedChargeAGibbsPerturbationProbability
    ring
  rw [hp, egbFixedChargeACriticalMarkov_affine_action]

/-- Centered Gibbs deviations are an exact scalar copy of the centered input dynamics. -/
theorem egbFixedChargeAGibbsPerturbation_centered (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeACriticalCenteredProfile n
      (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsPerturbationEnergy n f)) =
        fun i => (egbFixedChargeAGibbsPerturbationScale n f / (2 : ℝ) ^ (n + 3)) *
          egbFixedChargeACriticalCenteredProfile n
            ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) i := by
  funext i
  change egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsPerturbationEnergy n f) i -
    egbFixedChargeACriticalRealMean n
      (egbFixedChargeAGibbsMarkovPopulation n m 1 (egbFixedChargeAGibbsPerturbationEnergy n f)) = _
  rw [egbFixedChargeAGibbsPopulation_uniform_mean, egbFixedChargeAGibbsPerturbation_evolution,
    egbFixedChargeACriticalCenteredProfile_action]
  ring

/-- The entire centered-energy evolution embeds faithfully into Gibbs collision excess. -/
theorem egbFixedChargeAGibbsPerturbation_collision_identity (n m : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n m 1 (egbFixedChargeAGibbsPerturbationEnergy n f) =
      (egbFixedChargeAGibbsPerturbationScale n f / (2 : ℝ) ^ (n + 3)) ^ 2 *
        egbFixedChargeACriticalCenteredEnergy n
          ((egbFixedChargeACriticalMarkovIteratedKernel n m).toFinitePositiveKernel.applyReal f) := by
  rw [← egbFixedChargeAGibbsPopulation_centered_energy]
  simp only [egbFixedChargeACriticalCenteredEnergy, egbFixedChargeAGibbsPerturbation_centered,
    mul_pow, Finset.mul_sum]

/-- The initial collision excess records the original centered energy with a positive scale. -/
theorem egbFixedChargeAGibbsPerturbation_collision_initial (n : ℕ)
    (f : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsCollisionExcess n 0 1 (egbFixedChargeAGibbsPerturbationEnergy n f) =
      (egbFixedChargeAGibbsPerturbationScale n f / (2 : ℝ) ^ (n + 3)) ^ 2 *
        egbFixedChargeACriticalCenteredEnergy n f := by
  rw [egbFixedChargeAGibbsPerturbation_collision_identity,
    egbFixedChargeACriticalMarkovIteratedKernel_zero]

end
end GaloisForLFunctions.HTGeometry
