import GaloisForLFunctions.HilbertMetric.Probability.ThermalRobustness

/-!
# Thermal robustness from maximum likelihood

The largest likelihood ratio controls Pearson divergence and every stop-loss
transform. Its observable certificate combines the distance to each support
endpoint with the thermal variance. All bounds use the actual likelihood
ratio of an arbitrary competing law, so no domination assumption is needed.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Largest likelihood ratio relative to the faithful thermal law. -/
def thermalMaxLikelihood (β : ℝ) (E : ι → ℝ) (p : FiniteProbabilityLaw ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => p.prob i / finiteGibbsStateWeight β E i)

/-- Excess maximum likelihood, the nonlogarithmic order-infinity divergence. -/
def thermalMaxDivergence (β : ℝ) (E : ι → ℝ) (p : FiniteProbabilityLaw ι) : ℝ :=
  thermalMaxLikelihood β E p - 1

/-- Maximum value of an observable on its finite state space. -/
def finiteObservableMax (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- Minimum value of an observable on its finite state space. -/
def finiteObservableMin (f : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

theorem thermal_likelihood_le_max (β : ℝ) (E : ι → ℝ)
    (p : FiniteProbabilityLaw ι) (i : ι) :
    p.prob i / finiteGibbsStateWeight β E i ≤ thermalMaxLikelihood β E p := by
  exact Finset.le_sup' (fun j => p.prob j / finiteGibbsStateWeight β E j) (Finset.mem_univ i)

theorem thermal_prob_le_maxLikelihood (β : ℝ) (E : ι → ℝ)
    (p : FiniteProbabilityLaw ι) (i : ι) :
    p.prob i ≤ thermalMaxLikelihood β E p * finiteGibbsStateWeight β E i := by
  exact (div_le_iff₀ (finiteGibbsStateWeight_pos β E i)).mp
    (thermal_likelihood_le_max β E p i)

/-- Order-infinity divergence dominates the exact order-two divergence. -/
theorem thermalPearsonDivergence_le_maxDivergence (β : ℝ) (E : ι → ℝ)
    (p : FiniteProbabilityLaw ι) :
    thermalPearsonDivergence β E p ≤ thermalMaxDivergence β E p := by
  rw [thermalPearsonDivergence_eq]
  unfold thermalMaxDivergence
  apply sub_le_sub_right
  calc
    (∑ i, p.prob i ^ (2 : ℕ) / finiteGibbsStateWeight β E i) ≤
        ∑ i, p.prob i * thermalMaxLikelihood β E p := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (thermal_likelihood_le_max β E p i) (p.nonneg i)
      simpa only [pow_two, mul_div_assoc] using h
    _ = thermalMaxLikelihood β E p := by rw [← Finset.sum_mul, p.sum_prob, one_mul]

theorem thermalMaxDivergence_nonneg (β : ℝ) (E : ι → ℝ)
    (p : FiniteProbabilityLaw ι) : 0 ≤ thermalMaxDivergence β E p :=
  (pearsonEnergy_nonneg _ _).trans (thermalPearsonDivergence_le_maxDivergence β E p)

omit [Nonempty ι] in
/-- Subtracting a constant shifts a probability-weighted mean by that constant. -/
theorem finiteLaw_mean_sub_const (p : FiniteProbabilityLaw ι) (f : ι → ℝ) (c : ℝ) :
    finiteWeightedMean p.prob (fun i => f i - c) = finiteWeightedMean p.prob f - c := by
  simp only [finiteWeightedMean, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, p.sum_prob, one_mul]

/-- Every stop-loss transform gives a maximum-likelihood expectation certificate. -/
theorem thermal_expectation_le_stopLoss (β : ℝ) (E f : ι → ℝ)
    (p : FiniteProbabilityLaw ι) (c : ℝ) :
    finiteWeightedMean p.prob f ≤ c + thermalMaxLikelihood β E p *
      finiteWeightedMean (finiteGibbsStateWeight β E) (fun i => max (f i - c) 0) := by
  have h : finiteWeightedMean p.prob (fun i => f i - c) ≤
      thermalMaxLikelihood β E p *
        finiteWeightedMean (finiteGibbsStateWeight β E) (fun i => max (f i - c) 0) := by
    unfold finiteWeightedMean
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      p.prob i * (f i - c) ≤ p.prob i * max (f i - c) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (p.nonneg i)
      _ ≤ thermalMaxLikelihood β E p *
          (finiteGibbsStateWeight β E i * max (f i - c) 0) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (thermal_prob_le_maxLikelihood β E p i) (le_max_right _ _)
  rw [finiteLaw_mean_sub_const] at h
  linarith only [h]

/-- The support and variance bounds combine into the order-infinity certificate. -/
theorem thermal_expectation_shift_le_maxCertificate (β : ℝ) (E f : ι → ℝ)
    (p : FiniteProbabilityLaw ι) :
    finiteWeightedMean p.prob f - finiteWeightedMean (finiteGibbsStateWeight β E) f ≤
      min (thermalMaxDivergence β E p *
        (finiteWeightedMean (finiteGibbsStateWeight β E) f - finiteObservableMin f))
        (min (Real.sqrt (thermalMaxDivergence β E p *
          finiteWeightedVariance (finiteGibbsStateWeight β E) f))
          (finiteObservableMax f - finiteWeightedMean (finiteGibbsStateWeight β E) f)) := by
  have hlo (i : ι) : finiteObservableMin f ≤ f i :=
    Finset.inf'_le f (Finset.mem_univ i)
  have hhi (i : ι) : f i ≤ finiteObservableMax f :=
    Finset.le_sup' f (Finset.mem_univ i)
  apply le_min
  · have h := thermal_expectation_le_stopLoss β E f p (finiteObservableMin f)
    have hpos (i : ι) : max (f i - finiteObservableMin f) 0 = f i - finiteObservableMin f :=
      max_eq_left (sub_nonneg.mpr (hlo i))
    simp_rw [hpos] at h
    change finiteWeightedMean p.prob f ≤ finiteObservableMin f +
      thermalMaxLikelihood β E p *
        finiteWeightedMean (thermalLaw β E).prob (fun i => f i - finiteObservableMin f) at h
    rw [finiteLaw_mean_sub_const] at h
    change _ ≤ (thermalMaxLikelihood β E p - 1) * _
    change finiteWeightedMean p.prob f ≤ finiteObservableMin f +
      thermalMaxLikelihood β E p *
        (finiteWeightedMean (finiteGibbsStateWeight β E) f - finiteObservableMin f) at h
    nlinarith only [h]
  · apply le_min
    · apply (le_abs_self _).trans
      apply (thermal_expectation_shift_abs_le β E f p).trans
      apply Real.sqrt_le_sqrt
      exact mul_le_mul_of_nonneg_right (thermalPearsonDivergence_le_maxDivergence β E p)
        (Finset.sum_nonneg fun i _ =>
          mul_nonneg (finiteGibbsStateWeight_pos β E i).le (sq_nonneg _))
    · have h := thermal_expectation_le_stopLoss β E f p (finiteObservableMax f)
      have hzero (i : ι) : max (f i - finiteObservableMax f) 0 = 0 :=
        max_eq_right (sub_nonpos.mpr (hhi i))
      simp only [hzero, finiteWeightedMean,
        mul_zero, Finset.sum_const_zero, add_zero] at h
      exact sub_le_sub_right h _

end
end GaloisForLFunctions.HilbertMetric.Probability

#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_likelihood_le_max
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_prob_le_maxLikelihood
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermalPearsonDivergence_le_maxDivergence
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermalMaxDivergence_nonneg
#print axioms GaloisForLFunctions.HilbertMetric.Probability.finiteLaw_mean_sub_const
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_expectation_le_stopLoss
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_expectation_shift_le_maxCertificate
