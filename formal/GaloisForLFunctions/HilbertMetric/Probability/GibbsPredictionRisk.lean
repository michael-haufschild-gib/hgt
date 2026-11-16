import GaloisForLFunctions.HilbertMetric.Probability.BregmanCalibration
import GaloisForLFunctions.HilbertMetric.Probability.CriticalGibbsRobustness

/-!
# Prediction regret along the critical Gibbs chain

Bregman centering turns the corpus's observable error bound into an
estimation statement. The excess squared risk of the equilibrium forecast
decays geometrically and has a finite total budget along the actual chain.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Excess prediction loss incurred by using the uniform equilibrium forecast. -/
def criticalGibbsPredictionRegret (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) : ℝ :=
  bregmanRisk (criticalGibbsLaw n m β E) (fun t => t ^ (2 : ℕ)) f
      (finiteWeightedMean (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f) -
    bregmanRisk (criticalGibbsLaw n m β E) (fun t => t ^ (2 : ℕ)) f
      (finiteWeightedMean (criticalGibbsLaw n m β E).prob f)

/-- Exact excess risk, rather than a bound on the full prediction variance. -/
theorem criticalGibbsPredictionRegret_eq (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    criticalGibbsPredictionRegret n m β E f =
      criticalGibbsExpectationError n m β E f ^ (2 : ℕ) := by
  unfold criticalGibbsPredictionRegret
  rw [bregmanRisk_mean_split, scalarBregman_square]
  change _ = (finiteWeightedMean (criticalGibbsLaw n m β E).prob f -
    finiteWeightedMean (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f) ^ (2 : ℕ)
  ring

/-- The equilibrium forecast approaches the optimal forecast at the collision rate. -/
theorem criticalGibbsPredictionRegret_spectral_bound (n m : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    criticalGibbsPredictionRegret n m β E f ≤
      (4 / 9 : ℝ) ^ m *
        ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) *
          finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f := by
  rw [criticalGibbsPredictionRegret_eq]
  exact criticalGibbs_error_sq_spectral_bound n m β E f

/-- Summing prediction regrets over the entire chain costs only the initial collision excess. -/
theorem criticalGibbsPredictionRegret_total_bound (n : ℕ) (β : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    Summable (fun m => criticalGibbsPredictionRegret n m β E f) ∧
      (∑' m, criticalGibbsPredictionRegret n m β E f) ≤
        (9 / 5 : ℝ) * ((2 : ℝ) ^ (n + 3) * egbFixedChargeAGibbsCollisionExcess n 0 β E) *
          finiteWeightedVariance (uniformNoiseLaw (ι := Fin (2 ^ (n + 3)))).prob f := by
  simp only [criticalGibbsPredictionRegret_eq]
  exact criticalGibbs_error_sq_total_bound n β E f

/-- At every chain step, exponential and quartic estimation share the actual Gibbs mean. -/
theorem criticalGibbs_nonlinear_minimizers (n m : ℕ) (β q : ℝ)
    (E f : Fin (2 ^ (n + 3)) → ℝ) :
    ((∀ r, bregmanRisk (criticalGibbsLaw n m β E) quarticGenerator f q ≤
      bregmanRisk (criticalGibbsLaw n m β E) quarticGenerator f r) ↔
      q = finiteWeightedMean (criticalGibbsLaw n m β E).prob f) ∧
    ((∀ r, bregmanRisk (criticalGibbsLaw n m β E) Real.exp f q ≤
      bregmanRisk (criticalGibbsLaw n m β E) Real.exp f r) ↔
      q = finiteWeightedMean (criticalGibbsLaw n m β E).prob f) :=
  ⟨quarticRisk_minimizer_iff _ _ _, exponentialRisk_minimizer_iff _ _ _⟩

#print axioms criticalGibbsPredictionRegret_eq
#print axioms criticalGibbsPredictionRegret_spectral_bound
#print axioms criticalGibbsPredictionRegret_total_bound
#print axioms criticalGibbs_nonlinear_minimizers

end
end GaloisForLFunctions.HilbertMetric.Probability
