import GaloisForLFunctions.HilbertMetric.Probability.UniformNoiseRobustness
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsAccumulatedCollision

/-!
# Observable robustness along critical Gibbs Markov dynamics

The existing collision decay controls every observable through its uniform
variance. Squared expectation errors decay at the spectral rate and have a
finite accumulated budget, retaining the initial collision information.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- The existing critical Gibbs population as a probability law. -/
def criticalGibbsLaw (n m : ℕ) (β : ℝ) (E : Fin (2 ^ (n + 3)) → ℝ) :
    FiniteProbabilityLaw (Fin (2 ^ (n + 3))) where
  prob := egbFixedChargeAGibbsMarkovPopulation n m β E
  nonneg := egbFixedChargeAGibbsMarkovPopulation_nonneg n m β E
  sum_prob := egbFixedChargeAGibbsMarkovPopulation_mass n m β E

/-- Error of an observable relative to its uniform equilibrium expectation. -/
def criticalGibbsExpectationError (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  finiteWeightedMean (egbFixedChargeAGibbsMarkovPopulation n m β E) f -
    finiteWeightedMean (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f

/-- The Pearson divergence is the existing collision excess times dimension. -/
theorem criticalGibbs_uniformPearson_eq (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    uniformPearsonDivergence (criticalGibbsLaw n m β E) =
      (2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E := by
  rw [uniformPearsonDivergence, egbFixedChargeAGibbsCollisionExcess_identity]
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, criticalGibbsLaw]
  rw [mul_sub, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]

/-- Collision excess controls every observable with its own uniform variance. -/
theorem criticalGibbs_error_sq_le_collision (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    criticalGibbsExpectationError n m β E f ^ (2 : ℕ) ≤
      ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n m β E) *
        finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f := by
  have h := uniform_expectation_shift_sq_le (criticalGibbsLaw n m β E) f
  rwa [criticalGibbs_uniformPearson_eq] at h

/-- Every squared observable error inherits the explicit spectral decay rate. -/
theorem criticalGibbs_error_sq_spectral_bound (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    criticalGibbsExpectationError n m β E f ^ (2 : ℕ) ≤
      (4 / 9 : ℝ) ^ m *
        ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) *
          finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f := by
  apply (criticalGibbs_error_sq_le_collision n m β E f).trans
  have hv : 0 ≤ finiteWeightedVariance
      (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (uniformNoiseLaw.nonneg i) (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (egbFixedChargeAGibbsCollisionExcess_spectral_bound n m β E)
      (by positivity : 0 ≤ (2 : ℝ) ^ (n + 3))) hv
  convert h using 1 <;> ring

/-- The entire squared-error history has a variance-sensitive finite budget. -/
theorem criticalGibbs_error_sq_total_bound (n : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m => criticalGibbsExpectationError n m β E f ^ (2 : ℕ)) ∧
      (∑' m, criticalGibbsExpectationError n m β E f ^ (2 : ℕ)) ≤
        (9 / 5 : ℝ) * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) *
          finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f := by
  have hv : 0 ≤ finiteWeightedVariance
      (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f :=
    Finset.sum_nonneg fun i _ => mul_nonneg (uniformNoiseLaw.nonneg i) (sq_nonneg _)
  let K := (2 : ℝ) ^ (n + 3) *
    finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f
  have hK : 0 ≤ K := mul_nonneg (by positivity) hv
  have hs := (egbFixedChargeAGibbsCollisionExcess_summable n β E).mul_left K
  have hb (m : ℕ) : criticalGibbsExpectationError n m β E f ^ (2 : ℕ) ≤
      K * egbFixedChargeAGibbsCollisionExcess n m β E := by
    convert criticalGibbs_error_sq_le_collision n m β E f using 1 <;> dsimp [K] <;> ring
  have he := Summable.of_nonneg_of_le (fun m => sq_nonneg _) hb hs
  refine ⟨he, ?_⟩
  have ht := tsum_le_tsum hb he hs
  rw [tsum_mul_left] at ht
  have hc := mul_le_mul_of_nonneg_left
    (egbFixedChargeAGibbsCollisionExcess_total_bound n β E) hK
  apply (ht.trans hc).trans_eq
  dsimp [K]
  ring

end
end GaloisForLFunctions.HilbertMetric.Probability
