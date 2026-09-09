import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsEntropyMaximum

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter Topology

/-- Information remaining relative to the uniform stationary law. -/
def egbFixedChargeAGibbsEntropyDeficit (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  relEntropy (egbFixedChargeAGibbsMarkovPopulation n m β E)
    (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹)

/-- The cross entropy against the stationary law is independent of the energy landscape. -/
theorem egbFixedChargeAGibbsCrossEntropy_uniform (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    crossEntropy (egbFixedChargeAGibbsMarkovPopulation n m β E)
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) = (n + 3 : ℝ) * Real.log 2 := by
  simp only [crossEntropy, tsum_fintype, Real.log_inv, mul_neg, neg_neg]
  rw [← Finset.sum_mul, egbFixedChargeAGibbsMarkovPopulation_mass, one_mul, Real.log_pow]
  push_cast
  ring

/-- Relative entropy is exactly the shortfall from maximal Shannon entropy. -/
theorem egbFixedChargeAGibbsEntropyDeficit_identity (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsEntropyDeficit n m β E = (n + 3 : ℝ) * Real.log 2 -
      entropy (egbFixedChargeAGibbsMarkovPopulation n m β E) := by
  have h := entropy_add_relEntropy
    (p := fun _ : Fin (2 ^ (n + 3)) => ((2 : ℝ) ^ (n + 3))⁻¹)
    (egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E)
    (fun _ : Fin (2 ^ (n + 3)) => inv_pos.mpr (pow_pos (by norm_num) _))
    (hasSum_fintype _).summable (hasSum_fintype _).summable
  rw [egbFixedChargeAGibbsCrossEntropy_uniform] at h
  change entropy (egbFixedChargeAGibbsMarkovPopulation n m β E) +
    egbFixedChargeAGibbsEntropyDeficit n m β E = _ at h
  linarith

/-- No Gibbs population carries negative information relative to equilibrium. -/
theorem egbFixedChargeAGibbsEntropyDeficit_nonneg (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) : 0 ≤ egbFixedChargeAGibbsEntropyDeficit n m β E := by
  rw [egbFixedChargeAGibbsEntropyDeficit_identity]
  exact sub_nonneg.mpr (egbFixedChargeAGibbsEntropy_le_maximum n m β E)

/-- Every transition can only reduce the information remaining relative to equilibrium. -/
theorem egbFixedChargeAGibbsEntropyDeficit_antitone (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Antitone (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E) := by
  intro a b hab
  simp only [egbFixedChargeAGibbsEntropyDeficit_identity]
  linarith [egbFixedChargeAGibbsEntropy_monotone n β E hab]

/-- The complete information deficit vanishes at long times. -/
theorem egbFixedChargeAGibbsEntropyDeficit_limit (n : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m => egbFixedChargeAGibbsEntropyDeficit n m β E) atTop (nhds 0) := by
  simp only [egbFixedChargeAGibbsEntropyDeficit_identity]
  have hc : Tendsto (fun _ : ℕ => (n + 3 : ℝ) * Real.log 2) atTop
      (nhds ((n + 3 : ℝ) * Real.log 2)) := tendsto_const_nhds
  simpa using hc.sub (egbFixedChargeAGibbsEntropy_limit n β E)

end
end GaloisForLFunctions.HTGeometry
