import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsBistochasticEntropy

/-!
The critical Gibbs Markov evolution derived from arXiv:2609.00025 increases the
corpus Shannon entropy to its exact uniform value logN=(n+3)log2.
-/
namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The corpus Shannon entropy is continuous on all finite real arrays. -/
theorem egbFixedChargeAFiniteEntropy_continuous (n : ℕ) :
    Continuous (fun f : Fin n → ℝ => entropy f) := by
  have he (f : Fin n → ℝ) : entropy f = ∑ i : Fin n, Real.negMulLog (f i) := by
    simp only [entropy, tsum_fintype, Real.negMulLog, neg_mul]
  simp_rw [he]
  fun_prop

/-- The uniform law has exactly the logarithm of the number of grid states as entropy. -/
theorem egbFixedChargeAGibbsEntropy_uniform (n : ℕ) :
    entropy (fun _ : Fin (2 ^ (n + 3)) => ((2 : ℝ) ^ (n + 3))⁻¹) =
      (n + 3 : ℝ) * Real.log 2 := by
  simp only [entropy, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Real.log_inv]
  have hn : (2 : ℝ) ^ (n + 3) ≠ 0 := pow_ne_zero _ (by norm_num)
  have he : (2 : ℝ) ^ (n + 3) * (-(((2 : ℝ) ^ (n + 3))⁻¹ * -Real.log ((2 : ℝ) ^ (n + 3)))) =
      Real.log ((2 : ℝ) ^ (n + 3)) := by field_simp
  rw [he, Real.log_pow]
  push_cast
  ring

/-- Every finite Gibbs input reaches maximal Shannon entropy in the long-time limit. -/
theorem egbFixedChargeAGibbsEntropy_limit
    (n : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    Tendsto (fun m : ℕ => entropy (egbFixedChargeAGibbsMarkovPopulation n m β E)) atTop
      (𝓝 ((n + 3 : ℝ) * Real.log 2)) := by
  have h := (egbFixedChargeAFiniteEntropy_continuous (2 ^ (n + 3))).continuousAt.tendsto.comp
    (egbFixedChargeAGibbsMarkovPopulation_limit n β E)
  simpa only [Function.comp_def, egbFixedChargeAGibbsEntropy_uniform] using h

/-- No point of the Gibbs trajectory exceeds the exact uniform entropy bound. -/
theorem egbFixedChargeAGibbsEntropy_le_maximum
    (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    entropy (egbFixedChargeAGibbsMarkovPopulation n m β E) ≤ (n + 3 : ℝ) * Real.log 2 := by
  apply ge_of_tendsto (egbFixedChargeAGibbsEntropy_limit n β E)
  filter_upwards [eventually_ge_atTop m] with k hk
  exact egbFixedChargeAGibbsEntropy_monotone n β E hk

end

end GaloisForLFunctions.HTGeometry
