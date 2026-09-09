import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalHiddenProbabilityMixing

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite real energy landscape realizing the hidden positive probability law. -/
def egbFixedChargeAGibbsHiddenEnergy (n : ℕ) : Fin (2 ^ (n + 3)) → ℝ :=
  fun i => -Real.log (egbFixedChargeACriticalHiddenProbability n i)

/-- The explicit hidden energy has partition function one at unit inverse temperature. -/
theorem egbFixedChargeAGibbsHidden_partition (n : ℕ) :
    _root_.HTGeometry.finiteGibbsPartition 1 (egbFixedChargeAGibbsHiddenEnergy n) = 1 := by
  unfold _root_.HTGeometry.finiteGibbsPartition egbFixedChargeAGibbsHiddenEnergy
  simp only [neg_mul, one_mul, neg_neg]
  simp_rw [Real.exp_log (egbFixedChargeACriticalHiddenProbability_pos n _)]
  exact egbFixedChargeACriticalHiddenProbability_mass n

/-- The ordinary finite Gibbs construction recovers the hidden probability exactly. -/
theorem egbFixedChargeAGibbsHidden_realization (n : ℕ) :
    _root_.HTGeometry.finiteGibbsStateWeight 1 (egbFixedChargeAGibbsHiddenEnergy n) =
      egbFixedChargeACriticalHiddenProbability n := by
  funext i
  rw [_root_.HTGeometry.finiteGibbsStateWeight, egbFixedChargeAGibbsHidden_partition, div_one]
  simp only [egbFixedChargeAGibbsHiddenEnergy, neg_mul, one_mul, neg_neg]
  exact Real.exp_log (egbFixedChargeACriticalHiddenProbability_pos n i)

/-- Before mixing, the Gibbs population retains its nonuniform hidden perturbation. -/
theorem egbFixedChargeAGibbsHidden_initial (n : ℕ) :
    egbFixedChargeAGibbsMarkovPopulation n 0 1 (egbFixedChargeAGibbsHiddenEnergy n) =
      egbFixedChargeACriticalHiddenProbability n := by
  rw [egbFixedChargeAGibbsMarkovPopulation_zero, egbFixedChargeAGibbsHidden_realization]

/-- After the first transition the Gibbs population is exactly uniform forever. -/
theorem egbFixedChargeAGibbsHidden_finite_erasure (n m : ℕ) :
    egbFixedChargeAGibbsMarkovPopulation n (m + 1) 1 (egbFixedChargeAGibbsHiddenEnergy n) =
      (fun _ => ((2 : ℝ) ^ (n + 3))⁻¹) := by
  unfold egbFixedChargeAGibbsMarkovPopulation
  rw [egbFixedChargeAGibbsHidden_realization, egbFixedChargeACriticalHiddenProbability_erased]

end
end GaloisForLFunctions.HTGeometry
