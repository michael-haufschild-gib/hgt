import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatConvexRigidity
import GaloisForLFunctions.HilbertMetric.Probability.BregmanCalibration

/-!
# Flat prediction loss retains a whole half-line of minimizers

The flat potential of arXiv:2611.08616 applies to the corpus's finite
Bregman risk decomposition. Positive means have one optimal forecast;
nonpositive means have every nonpositive forecast as an optimum. Excess
risk controls the gradient displacement while retaining this exact
non-identifiability of the original forecast.
-/

namespace GaloisForLFunctions.HilbertMetric.Probability
open HTGeometry ExclusionOfTheCriticalState.FlatConvex
noncomputable section
variable {ι : Type*} [Fintype ι]

private theorem scalarBregman_flat (x q : ℝ) :
    scalarBregman potential x q = potential x - potential q - gradient q * (x - q) := by
  rw [scalarBregman, (potential_hasDerivAt q).deriv]

/-- Excess flat risk has both a transformed-error lower bound and a squared-bias upper bound. -/
theorem flatRisk_excess_bounds (p : FiniteProbabilityLaw ι) (x : ι → ℝ) (q : ℝ) :
    (gradient (finiteWeightedMean p.prob x) - gradient q) ^ 2 / 2 ≤
      bregmanRisk p potential x q - bregmanRisk p potential x (finiteWeightedMean p.prob x) ∧
    bregmanRisk p potential x q - bregmanRisk p potential x (finiteWeightedMean p.prob x) ≤
      (finiteWeightedMean p.prob x - q) ^ 2 / 2 := by
  rw [bregmanRisk_mean_split p potential x q, add_sub_cancel_left, scalarBregman_flat]
  exact ⟨gradient_displacement_le_tangent_error _ _, (tangent_error_bounds _ _).2⟩

/-- The full minimizer classification includes the entire flat half-line. -/
theorem flatRisk_minimizer_iff (p : FiniteProbabilityLaw ι) (x : ι → ℝ) (q : ℝ) :
    (∀ r, bregmanRisk p potential x q ≤ bregmanRisk p potential x r) ↔
      q = finiteWeightedMean p.prob x ∨ (finiteWeightedMean p.prob x ≤ 0 ∧ q ≤ 0) := by
  constructor
  · intro h
    have hb := h (finiteWeightedMean p.prob x)
    rw [bregmanRisk_mean_split p potential x q, scalarBregman_flat] at hb
    have hz : potential (finiteWeightedMean p.prob x) - potential q -
        gradient q * (finiteWeightedMean p.prob x - q) = 0 :=
      le_antisymm (by linarith only [hb]) (tangent_error_bounds _ _).1
    rcases (tangent_error_zero_iff _ _).mp hz with hq | hq
    · exact Or.inl hq.symm
    · exact Or.inr hq
  · intro h r
    have hz : scalarBregman potential (finiteWeightedMean p.prob x) q = 0 := by
      rw [scalarBregman_flat, tangent_error_zero_iff]
      rcases h with hq | hq
      · exact Or.inl hq.symm
      · exact Or.inr hq
    rw [bregmanRisk_mean_split p potential x q, hz, add_zero,
      bregmanRisk_mean_split p potential x r, scalarBregman_flat]
    exact le_add_of_nonneg_right (tangent_error_bounds _ _).1

/-- Although forecasts need not be identifiable, their flat gradients always are. -/
theorem flatRisk_minimizer_gradient_iff (p : FiniteProbabilityLaw ι)
    (x : ι → ℝ) (q : ℝ) :
    (∀ r, bregmanRisk p potential x q ≤ bregmanRisk p potential x r) ↔
      gradient q = gradient (finiteWeightedMean p.prob x) := by
  rw [flatRisk_minimizer_iff, gradient_eq_iff, and_comm]

#print axioms flatRisk_excess_bounds
#print axioms flatRisk_minimizer_iff
#print axioms flatRisk_minimizer_gradient_iff
end
end GaloisForLFunctions.HilbertMetric.Probability
