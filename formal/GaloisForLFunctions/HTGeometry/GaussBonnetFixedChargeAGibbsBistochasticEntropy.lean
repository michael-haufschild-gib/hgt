import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalMixingRigidity
import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications

/-!
Existing finite probability laws, majorization, and Shannon entropy applied to the
critical Gibbs transition family derived from arXiv:2609.00025. Temperatures and
energy arrays are arbitrary data; probability admission is proved internally.
-/
namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

noncomputable section

/-- Each transported Gibbs population as an existing corpus finite probability law. -/
def egbFixedChargeAGibbsProbabilityLaw (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : FiniteProbabilityLaw (Fin (2 ^ (n + 3))) where
  prob := egbFixedChargeAGibbsMarkovPopulation n m β E
  nonneg := egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E
  sum_prob := egbFixedChargeAGibbsMarkovPopulation_mass n m β E

/-- Corpus probability-law mixing is exactly the same Gibbs population evolution. -/
theorem egbFixedChargeAGibbsProbabilityLaw_mix
    (n a b : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    ((egbFixedChargeAGibbsProbabilityLaw n b β E).mix (egbFixedChargeACriticalBistochastic n a)).prob =
      egbFixedChargeAGibbsMarkovPopulation n (a + b) β E := by
  change (egbFixedChargeACriticalBistochastic n a).val *ᵥ
    egbFixedChargeAGibbsMarkovPopulation n b β E = _
  rw [egbFixedChargeACriticalBistochastic_action, egbFixedChargeAGibbsMarkovPopulation_add]

/-- Any further block of transitions increases the existing Shannon entropy. -/
theorem egbFixedChargeAGibbsEntropy_block_le
    (n a b : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n b β E) ≤
      entropy (egbFixedChargeAGibbsMarkovPopulation n (a + b) β E) := by
  have h := (egbFixedChargeAGibbsProbabilityLaw n b β E).entropy_le_mix
    (egbFixedChargeACriticalBistochastic n a)
  rw [egbFixedChargeAGibbsProbabilityLaw_mix] at h
  exact h

/-- Shannon entropy is monotone throughout the complete Gibbs population trajectory. -/
theorem egbFixedChargeAGibbsEntropy_monotone
    (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    Monotone (fun m : ℕ => entropy (egbFixedChargeAGibbsMarkovPopulation n m β E)) := by
  apply monotone_nat_of_le_succ
  intro m
  simpa only [Nat.add_comm 1 m] using egbFixedChargeAGibbsEntropy_block_le n 1 m β E

/-- Every largest-coordinate partial sum decreases along the Gibbs trajectory. -/
theorem egbFixedChargeAGibbsPopulation_majorization
    (n a b : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) (k : Fin (2 ^ (n + 3) + 1)) :
    topSum k.val (egbFixedChargeAGibbsMarkovPopulation n (a + b) β E) ≤
      topSum k.val (egbFixedChargeAGibbsMarkovPopulation n b β E) := by
  rw [egbFixedChargeAGibbsMarkovPopulation_add]
  exact egbFixedChargeACriticalMarkov_topSum_le n a
    (egbFixedChargeAGibbsMarkovPopulation n b β E) k

/-- Gibbs collision probability cannot increase under any number of transitions. -/
theorem egbFixedChargeAGibbsPopulation_collision_le
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    (∑ i, egbFixedChargeAGibbsMarkovPopulation n m β E i ^ 2) ≤
      ∑ i : Fin (2 ^ (n + 3)), _root_.HTGeometry.finiteGibbsStateWeight β E i ^ 2 :=
  egbFixedChargeACriticalMarkov_sum_sq_le n m _

end

end GaloisForLFunctions.HTGeometry
