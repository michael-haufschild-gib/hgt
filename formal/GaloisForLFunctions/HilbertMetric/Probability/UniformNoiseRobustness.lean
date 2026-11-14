import GaloisForLFunctions.HilbertMetric.Probability.PearsonRobustness
import GaloisForLFunctions.HTGeometry.FiniteNoiseInformationBoundary

/-!
# Collision-controlled robustness under bistochastic noise

Pearson divergence from the uniform law is cardinality times collision
probability minus one. Thus collision contraction gives a monotone
variance-sensitive certificate for every observable under bistochastic noise.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Pearson divergence from uniform, expressed through collision probability. -/
def uniformPearsonDivergence (p : FiniteProbabilityLaw ι) : ℝ :=
  (Fintype.card ι : ℝ) * (∑ i, p.prob i ^ (2 : ℕ)) - 1

/-- The collision expression is the literal Pearson energy of the likelihood. -/
theorem uniformPearsonDivergence_eq_energy (p : FiniteProbabilityLaw ι) :
    uniformPearsonDivergence p =
      pearsonEnergy uniformNoiseLaw (fun i => (Fintype.card ι : ℝ) * p.prob i) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold pearsonEnergy uniformNoiseLaw
  simp_rw [show ∀ i, (Fintype.card ι : ℝ)⁻¹ *
      ((Fintype.card ι : ℝ) * p.prob i - 1) ^ (2 : ℕ) =
      (Fintype.card ι : ℝ) * p.prob i ^ (2 : ℕ) - 2 * p.prob i +
        (Fintype.card ι : ℝ)⁻¹ by intro i; field_simp [hn]; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, p.sum_prob]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]
  unfold uniformPearsonDivergence
  ring

theorem uniformPearsonDivergence_nonneg (p : FiniteProbabilityLaw ι) :
    0 ≤ uniformPearsonDivergence p := by
  rw [uniformPearsonDivergence_eq_energy]
  exact pearsonEnergy_nonneg _ _

/-- Bistochastic noise contracts the exact divergence governing the certificate. -/
theorem uniformPearsonDivergence_mix_le (p : FiniteProbabilityLaw ι)
    (M : Matrix.doublyStochastic ℝ ι) :
    uniformPearsonDivergence (p.mix M) ≤ uniformPearsonDivergence p := by
  unfold uniformPearsonDivergence
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left (p.collision_mix_le M) (by positivity)) 1

/-- The likelihood of any law relative to uniform recovers its expectations. -/
theorem uniform_likelihood_expectation (p : FiniteProbabilityLaw ι) (f : ι → ℝ) :
    finiteWeightedMean (uniformNoiseLaw (ι := ι)).prob
        (fun i => ((Fintype.card ι : ℝ) * p.prob i) * f i) =
      finiteWeightedMean p.prob f := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteWeightedMean uniformNoiseLaw
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hn]

/-- Collision probability gives a variance-sensitive error bound for every observable. -/
theorem uniform_expectation_shift_sq_le (p : FiniteProbabilityLaw ι) (f : ι → ℝ) :
    (finiteWeightedMean p.prob f - finiteWeightedMean (uniformNoiseLaw (ι := ι)).prob f) ^
        (2 : ℕ) ≤
      uniformPearsonDivergence p * finiteWeightedVariance (uniformNoiseLaw (ι := ι)).prob f := by
  have hm : finiteWeightedMean (uniformNoiseLaw (ι := ι)).prob
      (fun i => (Fintype.card ι : ℝ) * p.prob i) = 1 := by
    have h := uniform_likelihood_expectation p (fun _ => 1)
    simpa only [mul_one, finiteWeightedMean, p.sum_prob] using h
  have h := likelihood_expectation_shift_sq_le uniformNoiseLaw
    (fun i => (Fintype.card ι : ℝ) * p.prob i) f
  rwa [uniform_likelihood_expectation, hm, one_mul,
    ← uniformPearsonDivergence_eq_energy] at h

/-- After arbitrary bistochastic noise the original collision certificate still applies. -/
theorem mixed_uniform_expectation_shift_sq_le (p : FiniteProbabilityLaw ι)
    (M : Matrix.doublyStochastic ℝ ι) (f : ι → ℝ) :
    (finiteWeightedMean (p.mix M).prob f -
        finiteWeightedMean (uniformNoiseLaw (ι := ι)).prob f) ^ (2 : ℕ) ≤
      uniformPearsonDivergence p * finiteWeightedVariance (uniformNoiseLaw (ι := ι)).prob f := by
  apply (uniform_expectation_shift_sq_le (p.mix M) f).trans
  apply mul_le_mul_of_nonneg_right (uniformPearsonDivergence_mix_le p M)
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (uniformNoiseLaw.nonneg i) (sq_nonneg _)

end
end GaloisForLFunctions.HilbertMetric.Probability

#print axioms GaloisForLFunctions.HilbertMetric.Probability.uniformPearsonDivergence_eq_energy
#print axioms GaloisForLFunctions.HilbertMetric.Probability.uniformPearsonDivergence_nonneg
#print axioms GaloisForLFunctions.HilbertMetric.Probability.uniformPearsonDivergence_mix_le
#print axioms GaloisForLFunctions.HilbertMetric.Probability.uniform_likelihood_expectation
#print axioms GaloisForLFunctions.HilbertMetric.Probability.uniform_expectation_shift_sq_le
#print axioms GaloisForLFunctions.HilbertMetric.Probability.mixed_uniform_expectation_shift_sq_le
