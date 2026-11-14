import GaloisForLFunctions.HilbertMetric.Probability.ThermalRobustness
import GaloisForLFunctions.HTGeometry.ChargedStringGibbsVariance
import GaloisForLFunctions.HTGeometry.ReplicaObserverActionCrowding

/-!
# Robustness of sampled charged-string potentials

The finite thermal variance bounds for the exterior electrostatic potential
control its expectation under every competing probability law. The error is
scaled by Pearson divergence from the reference Gibbs population.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.CPV _root_.HTGeometry
noncomputable section

/-- Centered finite variance agrees with the existing thermal Fisher variance. -/
theorem thermalWeightedVariance_eq_energyVariance {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (E : ι → ℝ) :
    finiteWeightedVariance (finiteGibbsStateWeight β E) E = finiteGibbsEnergyVariance β E := by
  exact weighted_variance_eq (sum_finiteGibbsStateWeight_eq_one β E) E

/-- The sampled potential inherits the full variance-sensitive robustness bound. -/
theorem stringPotential_expectation_shift_sq_le_variance {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) (p : FiniteProbabilityLaw (Fin (n + 1))) :
    (finiteWeightedMean p.prob (stringPotentialSpectrum ell tau x) -
        finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x)) ^ (2 : ℕ) ≤
      thermalPearsonDivergence β (stringPotentialSpectrum ell tau x) p *
        finiteGibbsEnergyVariance β (stringPotentialSpectrum ell tau x) := by
  have h := thermal_expectation_shift_sq_le β (stringPotentialSpectrum ell tau x)
    (stringPotentialSpectrum ell tau x) p
  rwa [thermalWeightedVariance_eq_energyVariance] at h

/-- Coherent radius gives a uniform electrostatic robustness certificate. -/
theorem stringPotential_expectation_shift_sq_le_radius {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) (p : FiniteProbabilityLaw (Fin (n + 1))) :
    (finiteWeightedMean p.prob (stringPotentialSpectrum ell tau x) -
        finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x)) ^ (2 : ℕ) ≤
      thermalPearsonDivergence β (stringPotentialSpectrum ell tau x) p *
        (coherentRadius tau ^ (2 : ℕ) / 4) := by
  apply (stringPotential_expectation_shift_sq_le_variance β ell tau x p).trans
  exact mul_le_mul_of_nonneg_left (stringPotentialSpectrum_variance_bound β ell tau x).le
    (pearsonEnergy_nonneg _ _)

/-- The charge-temperature identity expresses the same certificate in horizon data. -/
theorem stringPotential_expectation_shift_sq_le_temperature {n : ℕ}
    (β ell tau : ℝ) (x : Fin (n + 1) → ℝ) (p : FiniteProbabilityLaw (Fin (n + 1))) :
    (finiteWeightedMean p.prob (stringPotentialSpectrum ell tau x) -
        finiteGibbsEnergyMean β (stringPotentialSpectrum ell tau x)) ^ (2 : ℕ) ≤
      thermalPearsonDivergence β (stringPotentialSpectrum ell tau x) p *
        ((1 - 4 * Real.pi * stringBlackHoleTemperature ell tau / Real.exp ell) / 4) := by
  apply (stringPotential_expectation_shift_sq_le_variance β ell tau x p).trans
  exact mul_le_mul_of_nonneg_left
    (stringPotentialSpectrum_variance_temperature_bound β ell tau x).le (pearsonEnergy_nonneg _ _)

end
end GaloisForLFunctions.HilbertMetric.Probability
