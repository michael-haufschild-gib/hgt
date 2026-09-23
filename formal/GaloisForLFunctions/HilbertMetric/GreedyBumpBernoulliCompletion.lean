import GaloisForLFunctions.HilbertMetric.TransverseDegreePhase
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump factorial cumulants in Bernoulli graph completions

The Bernoulli channels in quadratic graph completion are one-point exclusion laws.  Their first
two factorial cumulants reconstruct the completion mean and variance, while their negative pair
cumulant is exactly the non-baseline Fano margin.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite family of genuine Bernoulli completion channels. -/
structure GreedyBumpBernoulliCompletionData (ι : Type*) [Fintype ι] where
  probability : ι → ℝ
  probability_nonneg : ∀ i, 0 ≤ probability i
  probability_lt_one : ∀ i, probability i < 1

/-- Strict one-point probability carried by a completion channel. -/
def GreedyBumpBernoulliCompletionData.channelProbability
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) (i : ι) :
    StrictProbabilityParameter :=
  ⟨data.probability i, data.probability_nonneg i, data.probability_lt_one i⟩

/-- Point-count law carried by one completion channel. -/
def GreedyBumpBernoulliCompletionData.channelCount
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) (i : ι) :
    FinitePointCountLaw Bool :=
  greedyBumpBernoulliExclusion (data.channelProbability i).toProbabilityParameter

/-- First channel factorial cumulant. -/
theorem GreedyBumpBernoulliCompletionData.channel_cumulantOne
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) (i : ι) :
    (data.channelCount i).factorialCumulantOne = data.probability i := by
  simpa [GreedyBumpBernoulliCompletionData.channelCount,
    GreedyBumpBernoulliCompletionData.channelProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    greedyBumpBernoulli_factorialCumulantOne
      (data.channelProbability i).toProbabilityParameter

/-- Second channel factorial cumulant. -/
theorem GreedyBumpBernoulliCompletionData.channel_cumulantTwo
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) (i : ι) :
    (data.channelCount i).factorialCumulantTwo = -(data.probability i) ^ (2 : ℕ) := by
  simpa [GreedyBumpBernoulliCompletionData.channelCount,
    GreedyBumpBernoulliCompletionData.channelProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    greedyBumpBernoulli_factorialCumulantTwo
      (data.channelProbability i).toProbabilityParameter

/-- Completion mean is baseline plus sum of first factorial cumulants. -/
theorem GreedyBumpBernoulliCompletionData.mean_eq_baseline_add_sum_cumulantOne
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (baseline : ℝ) :
    bernoulliCompletionMean baseline data.probability =
      baseline + ∑ i, (data.channelCount i).factorialCumulantOne := by
  unfold bernoulliCompletionMean
  apply congrArg (baseline + ·)
  apply Finset.sum_congr rfl
  intro i hi
  simpa [GreedyBumpBernoulliCompletionData.channelCount,
    GreedyBumpBernoulliCompletionData.channelProbability,
    StrictProbabilityParameter.toProbabilityParameter] using
    (greedyBumpBernoulli_factorialCumulantOne
      (data.channelProbability i).toProbabilityParameter).symm

/-- Completion variance is sum of first plus second factorial cumulants. -/
theorem GreedyBumpBernoulliCompletionData.variance_eq_sum_cumulantOne_add_cumulantTwo
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) :
    bernoulliCompletionVariance data.probability =
      ∑ i, ((data.channelCount i).factorialCumulantOne +
        (data.channelCount i).factorialCumulantTwo) := by
  unfold bernoulliCompletionVariance
  apply Finset.sum_congr rfl
  intro i hi
  simp only [GreedyBumpBernoulliCompletionData.channelCount]
  rw [greedyBumpBernoulli_factorialCumulantOne,
    greedyBumpBernoulli_factorialCumulantTwo]
  change data.probability i * (1 - data.probability i) =
    data.probability i + -(data.probability i) ^ (2 : ℕ)
  ring

/-- Pair factorial cumulants are exactly the negative squared channel probabilities. -/
theorem GreedyBumpBernoulliCompletionData.sum_cumulantTwo_eq_neg_sum_sq
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) :
    (∑ i, (data.channelCount i).factorialCumulantTwo) =
      -(∑ i, (data.probability i) ^ (2 : ℕ)) := by
  calc
    (∑ i, (data.channelCount i).factorialCumulantTwo) =
        ∑ i, -(data.probability i) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [GreedyBumpBernoulliCompletionData.channelCount,
            GreedyBumpBernoulliCompletionData.channelProbability,
            StrictProbabilityParameter.toProbabilityParameter] using
            greedyBumpBernoulli_factorialCumulantTwo
              (data.channelProbability i).toProbabilityParameter
    _ = -(∑ i, (data.probability i) ^ (2 : ℕ)) := by
      rw [Finset.sum_neg_distrib]

/-- Paper's negative pair correction is precisely the non-baseline Bernoulli Fano margin. -/
theorem GreedyBumpBernoulliCompletionData.fanoMargin_eq_baseline_sub_sum_cumulantTwo
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (baseline : ℝ) :
    bernoulliCompletionMean baseline data.probability -
        bernoulliCompletionVariance data.probability =
      baseline - ∑ i, (data.channelCount i).factorialCumulantTwo := by
  rw [bernoulliCompletion_fano_identity, data.sum_cumulantTwo_eq_neg_sum_sq]
  ring

/-- Full all-order correction across completion channels is log of their joint void factor. -/
theorem GreedyBumpBernoulliCompletionData.totalCumulantSeries_eq_log_voidProduct
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι) :
    (∑ i : ι, ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
      (data.channelProbability i) k) =
      Real.log (∏ i : ι, (1 - data.probability i)) := by
  calc
    (∑ i : ι, ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
        (data.channelProbability i) k) =
        ∑ i : ι, Real.log (1 - data.probability i) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [GreedyBumpBernoulliCompletionData.channelProbability] using
            (greedyBumpBernoulli_logVoidSeries_hasSum
              (data.channelProbability i)).tsum_eq
    _ = Real.log (∏ i : ι, (1 - data.probability i)) := by
      symm
      rw [Real.log_prod]
      intro i hi
      exact ne_of_gt (sub_pos.mpr (data.probability_lt_one i))

/-- Transverse-channel mean in first-factorial-cumulant coordinates. -/
theorem GreedyBumpBernoulliCompletionData.transverseMean_eq_cumulantOne
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (loweringCharge topDegree : ℝ) :
    transverseChannelMean loweringCharge topDegree data.probability =
      loweringCharge + ∑ i,
        (1 + (topDegree - 1) * (data.channelCount i).factorialCumulantOne) := by
  unfold transverseChannelMean
  apply congrArg (loweringCharge + ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [data.channel_cumulantOne]

/-- Transverse-channel variance in first-plus-second factorial-cumulant coordinates. -/
theorem GreedyBumpBernoulliCompletionData.transverseVariance_eq_cumulants
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (topDegree : ℝ) :
    transverseChannelVariance topDegree data.probability =
      ∑ i, (topDegree - 1) ^ (2 : ℕ) *
        ((data.channelCount i).factorialCumulantOne +
          (data.channelCount i).factorialCumulantTwo) := by
  unfold transverseChannelVariance
  apply Finset.sum_congr rfl
  intro i hi
  rw [data.channel_cumulantOne, data.channel_cumulantTwo]
  ring

/-- Unequal-gap completion mean in factorial-cumulant coordinates. -/
theorem GreedyBumpBernoulliCompletionData.unequalGapMean_eq_cumulantOne
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (loweringCharge : ℝ) (lowerDegree gap : ι → ℝ) :
    unequalGapChannelMean loweringCharge lowerDegree gap data.probability =
      loweringCharge + ∑ i,
        (lowerDegree i + gap i * (data.channelCount i).factorialCumulantOne) := by
  unfold unequalGapChannelMean
  apply congrArg (loweringCharge + ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [data.channel_cumulantOne]

/-- Unequal-gap completion variance in first-plus-second factorial-cumulant coordinates. -/
theorem GreedyBumpBernoulliCompletionData.unequalGapVariance_eq_cumulants
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (gap : ι → ℝ) :
    unequalGapChannelVariance gap data.probability =
      ∑ i, (gap i) ^ (2 : ℕ) *
        ((data.channelCount i).factorialCumulantOne +
          (data.channelCount i).factorialCumulantTwo) := by
  unfold unequalGapChannelVariance
  apply Finset.sum_congr rfl
  intro i hi
  rw [data.channel_cumulantOne, data.channel_cumulantTwo]
  ring

/-- Entire unequal-gap Fano law rewritten as deterministic terms plus paper's first two connected
count corrections. -/
theorem GreedyBumpBernoulliCompletionData.unequalGapFanoMargin_eq_cumulants
    {ι : Type*} [Fintype ι] (data : GreedyBumpBernoulliCompletionData ι)
    (loweringCharge : ℝ) (lowerDegree gap : ι → ℝ) :
    unequalGapChannelFanoMargin loweringCharge lowerDegree gap data.probability =
      loweringCharge + ∑ i,
        (lowerDegree i + gap i * (data.channelCount i).factorialCumulantOne -
          (gap i) ^ (2 : ℕ) * ((data.channelCount i).factorialCumulantOne +
            (data.channelCount i).factorialCumulantTwo)) := by
  simp_rw [data.channel_cumulantOne, data.channel_cumulantTwo]
  unfold unequalGapChannelFanoMargin unequalGapChannelMean unequalGapChannelVariance
  rw [show loweringCharge + (∑ i, (lowerDegree i + gap i * data.probability i)) -
      (∑ i, (gap i ^ (2 : ℕ) * data.probability i * (1 - data.probability i))) =
      loweringCharge + ((∑ i, (lowerDegree i + gap i * data.probability i)) -
        (∑ i, (gap i ^ (2 : ℕ) * data.probability i * (1 - data.probability i)))) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (loweringCharge + ·)
  apply Finset.sum_congr rfl
  intro i hi
  ring

end

end GaloisForLFunctions.HilbertMetric
