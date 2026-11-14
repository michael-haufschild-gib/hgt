import GaloisForLFunctions.HilbertMetric.Probability.UniformNoiseRobustness

/-!
# Two-sided collision certificates for group noise

Convolution on a finite group is bistochastic in either input. Consequently
the variance-sensitive Pearson robustness certificate is bounded by the
smaller of the two input collision divergences, including noncommutative groups.
-/

open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HilbertMetric.Probability
noncomputable section
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Right-increment noise, complementary to the existing left-increment kernel. -/
def rightGroupNoise (p : FiniteProbabilityLaw G) : doublyStochastic ℝ G := by
  refine ⟨fun i j => p.prob (j⁻¹ * i), mem_doublyStochastic_iff_sum.mpr
    ⟨fun i j => p.nonneg _, ?_, ?_⟩⟩
  · intro i
    exact ((Equiv.inv G |>.trans (Equiv.mulRight i)).sum_comp p.prob).trans p.sum_prob
  · intro j
    exact (Equiv.sum_comp (Equiv.mulLeft j⁻¹) p.prob).trans p.sum_prob

/-- Convolution can be realized as noise acting on either input. -/
theorem groupNoise_right_eq_left (p q : FiniteProbabilityLaw G) :
    (p.mix (rightGroupNoise q)).prob = (q.mix (relativeGroupNoise p)).prob := by
  funext i
  change (∑ j, q.prob (j⁻¹ * i) * p.prob j) = ∑ j, p.prob (i * j⁻¹) * q.prob j
  have h := (Equiv.inv G |>.trans (Equiv.mulLeft i)).sum_comp
    (fun j => q.prob (j⁻¹ * i) * p.prob j)
  change (∑ j, q.prob ((i * j⁻¹)⁻¹ * i) * p.prob (i * j⁻¹)) =
    (∑ j, q.prob (j⁻¹ * i) * p.prob j) at h
  simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one, mul_comm]
    using h.symm

/-- Group convolution contracts Pearson divergence relative to both input laws. -/
theorem groupNoise_uniformPearson_le_min (p q : FiniteProbabilityLaw G) :
    uniformPearsonDivergence (q.mix (relativeGroupNoise p)) ≤
      min (uniformPearsonDivergence p) (uniformPearsonDivergence q) := by
  apply le_min
  · have h := uniformPearsonDivergence_mix_le p (rightGroupNoise q)
    unfold uniformPearsonDivergence at h ⊢
    rwa [groupNoise_right_eq_left] at h
  · exact uniformPearsonDivergence_mix_le q (relativeGroupNoise p)

/-- Every observable of a noisy group law obeys the sharper input certificate. -/
theorem groupNoise_expectation_shift_sq_le_min (p q : FiniteProbabilityLaw G) (f : G → ℝ) :
    (finiteWeightedMean (q.mix (relativeGroupNoise p)).prob f -
        finiteWeightedMean (uniformNoiseLaw (ι := G)).prob f) ^ (2 : ℕ) ≤
      min (uniformPearsonDivergence p) (uniformPearsonDivergence q) *
        finiteWeightedVariance (uniformNoiseLaw (ι := G)).prob f := by
  apply (uniform_expectation_shift_sq_le (q.mix (relativeGroupNoise p)) f).trans
  apply mul_le_mul_of_nonneg_right (groupNoise_uniformPearson_le_min p q)
  exact Finset.sum_nonneg fun i _ => mul_nonneg (uniformNoiseLaw.nonneg i) (sq_nonneg _)

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
