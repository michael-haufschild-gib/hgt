import GaloisForLFunctions.RHTower.SpurCumulantBounds
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump factorial cumulants in the spur rescaling product

The spur multiplier `∏_{i<j} (1-i/d)` is exactly the joint void probability of independent
one-point exclusion channels with probabilities `i/d`.  The factorial-cumulant expansion from
arXiv:2609.03581 therefore identifies the corpus's `cumulantLogPoly` as the positive negative-log
void truncation, order by order.
-/

open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Certified live-range spur hazard schedule. -/
structure GreedyBumpSpurHazardData where
  denominator : ℕ
  depth : ℕ
  denominator_pos : 0 < denominator
  depth_le_denominator : depth ≤ denominator

/-- Bernoulli hazard `i/d` at rescaling step `i`. -/
def GreedyBumpSpurHazardData.probability
    (data : GreedyBumpSpurHazardData) (i : Fin data.depth) : ℝ :=
  (i : ℝ) / (data.denominator : ℝ)

theorem GreedyBumpSpurHazardData.probability_nonnegative
    (data : GreedyBumpSpurHazardData) (i : Fin data.depth) :
    0 ≤ data.probability i := by
  exact div_nonneg (by positivity) (by positivity)

theorem GreedyBumpSpurHazardData.probability_lt_one
    (data : GreedyBumpSpurHazardData) (i : Fin data.depth) :
    data.probability i < 1 := by
  rw [GreedyBumpSpurHazardData.probability,
    div_lt_one (by exact_mod_cast data.denominator_pos)]
  exact_mod_cast lt_of_lt_of_le i.isLt data.depth_le_denominator

/-- Spur hazard as a strict one-point exclusion probability. -/
def GreedyBumpSpurHazardData.strictProbability
    (data : GreedyBumpSpurHazardData) (i : Fin data.depth) :
    StrictProbabilityParameter :=
  ⟨data.probability i, data.probability_nonnegative i, data.probability_lt_one i⟩

/-- Point-count law of one spur hazard. -/
def GreedyBumpSpurHazardData.channelCount
    (data : GreedyBumpSpurHazardData) (i : Fin data.depth) :
    FinitePointCountLaw Bool :=
  greedyBumpBernoulliExclusion (data.strictProbability i).toProbabilityParameter

/-- Product of no-hazard probabilities is the original live-range spur multiplier. -/
theorem GreedyBumpSpurHazardData.voidProduct_eq_spurProduct
    (data : GreedyBumpSpurHazardData) :
    (∏ i : Fin data.depth, (1 - data.probability i)) =
      ∏ i ∈ Finset.range data.depth,
        (1 - (i : ℝ) / (data.denominator : ℝ)) := by
  simpa only [GreedyBumpSpurHazardData.probability] using
    (Fin.prod_univ_eq_prod_range
      (fun i => 1 - (i : ℝ) / (data.denominator : ℝ)) data.depth)

/-- First connected count correction is the normalized first spur power sum. -/
theorem GreedyBumpSpurHazardData.sum_cumulantOne
    (data : GreedyBumpSpurHazardData) :
    (∑ i : Fin data.depth,
      ((data.channelCount i).factorialCumulantOne)) =
      rescalePowerSum 1 data.depth / (data.denominator : ℝ) := by
  calc
    (∑ i : Fin data.depth, (data.channelCount i).factorialCumulantOne) =
        ∑ i : Fin data.depth, data.probability i := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [GreedyBumpSpurHazardData.channelCount,
            GreedyBumpSpurHazardData.strictProbability,
            StrictProbabilityParameter.toProbabilityParameter] using
            greedyBumpBernoulli_factorialCumulantOne
              (data.strictProbability i).toProbabilityParameter
    _ = rescalePowerSum 1 data.depth / (data.denominator : ℝ) := by
      rw [show (∑ i : Fin data.depth, data.probability i) =
          ∑ i ∈ Finset.range data.depth,
            ((i : ℝ) / (data.denominator : ℝ)) by
        simpa only [GreedyBumpSpurHazardData.probability] using
          (Fin.sum_univ_eq_sum_range
            (fun i => (i : ℝ) / (data.denominator : ℝ)) data.depth)]
      simp only [rescalePowerSum]
      rw [Finset.sum_div]
      simp

/-- Pair correction is the negative normalized second spur power sum. -/
theorem GreedyBumpSpurHazardData.sum_cumulantTwo
    (data : GreedyBumpSpurHazardData) :
    (∑ i : Fin data.depth,
      ((data.channelCount i).factorialCumulantTwo)) =
      -(rescalePowerSum 2 data.depth / (data.denominator : ℝ) ^ (2 : ℕ)) := by
  calc
    (∑ i : Fin data.depth, (data.channelCount i).factorialCumulantTwo) =
        ∑ i : Fin data.depth, -(data.probability i) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [GreedyBumpSpurHazardData.channelCount,
            GreedyBumpSpurHazardData.strictProbability,
            StrictProbabilityParameter.toProbabilityParameter] using
            greedyBumpBernoulli_factorialCumulantTwo
              (data.strictProbability i).toProbabilityParameter
    _ = -(rescalePowerSum 2 data.depth / (data.denominator : ℝ) ^ (2 : ℕ)) := by
      rw [show (∑ i : Fin data.depth, -(data.probability i) ^ (2 : ℕ)) =
          ∑ i ∈ Finset.range data.depth,
            -(((i : ℝ) / (data.denominator : ℝ)) ^ (2 : ℕ)) by
        simpa only [GreedyBumpSpurHazardData.probability] using
          (Fin.sum_univ_eq_sum_range
            (fun i => -(((i : ℝ) / (data.denominator : ℝ)) ^ (2 : ℕ))) data.depth)]
      rw [Finset.sum_neg_distrib]
      apply congrArg Neg.neg
      simp only [rescalePowerSum]
      simp_rw [div_pow]
      rw [Finset.sum_div]

/-- Complete connected correction series is exactly log of the spur multiplier. -/
theorem GreedyBumpSpurHazardData.cumulantSeries_eq_log_spurProduct
    (data : GreedyBumpSpurHazardData) :
    (∑ i : Fin data.depth, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution
        (data.strictProbability i) k) =
      Real.log (∏ i ∈ Finset.range data.depth,
        (1 - (i : ℝ) / (data.denominator : ℝ))) := by
  rw [← data.voidProduct_eq_spurProduct, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro i hi
    simpa [GreedyBumpSpurHazardData.strictProbability] using
      (greedyBumpBernoulli_logVoidSeries_hasSum
        (data.strictProbability i)).tsum_eq
  · intro i hi
    exact ne_of_gt (sub_pos.mpr (data.probability_lt_one i))

/-- Sum of order-`k+1` connected hazard contributions is one spur power-sum term. -/
theorem GreedyBumpSpurHazardData.orderContribution_eq
    (data : GreedyBumpSpurHazardData) (k : ℕ) :
    (∑ i : Fin data.depth, greedyBumpBernoulliLogVoidContribution
      (data.strictProbability i) k) =
      -(rescalePowerSum (k + 1) data.depth /
        ((k + 1 : ℝ) * (data.denominator : ℝ) ^ (k + 1))) := by
  simp_rw [greedyBumpBernoulli_logVoidContribution_eq]
  rw [show (∑ i : Fin data.depth,
      -((data.strictProbability i : ℝ) ^ (k + 1) / (k + 1))) =
      ∑ i ∈ Finset.range data.depth,
        -((((i : ℝ) / (data.denominator : ℝ)) ^ (k + 1)) / (k + 1)) by
    simpa only [GreedyBumpSpurHazardData.strictProbability,
      GreedyBumpSpurHazardData.probability] using
      (Fin.sum_univ_eq_sum_range
        (fun i => -((((i : ℝ) / (data.denominator : ℝ)) ^ (k + 1)) /
          (k + 1))) data.depth)]
  rw [Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  simp_rw [div_pow]
  simp_rw [div_div]
  calc
    (∑ i ∈ Finset.range data.depth,
        (i : ℝ) ^ (k + 1) /
          ((data.denominator : ℝ) ^ (k + 1) * (k + 1 : ℝ))) =
        (∑ i ∈ Finset.range data.depth, (i : ℝ) ^ (k + 1)) /
          ((data.denominator : ℝ) ^ (k + 1) * (k + 1 : ℝ)) :=
      (Finset.sum_div (Finset.range data.depth)
        (fun i => (i : ℝ) ^ (k + 1))
        ((data.denominator : ℝ) ^ (k + 1) * (k + 1 : ℝ))).symm
    _ = rescalePowerSum (k + 1) data.depth /
        ((k + 1 : ℝ) * (data.denominator : ℝ) ^ (k + 1)) := by
      simp only [rescalePowerSum]
      ring

/-- Finite connected series is exactly negative `cumulantLogPoly` at `1/d`. -/
theorem GreedyBumpSpurHazardData.truncatedSeries_eq_neg_cumulantLogPoly
    (data : GreedyBumpSpurHazardData) (n : ℕ) :
    (∑ i : Fin data.depth, ∑ k ∈ Finset.range n,
      greedyBumpBernoulliLogVoidContribution
        (data.strictProbability i) k) =
      -(cumulantLogPoly n data.depth).eval
        ((data.denominator : ℝ)⁻¹) := by
  rw [Finset.sum_comm]
  rw [eval_cumulantLogPoly_inv_nat data.denominator_pos]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [data.orderContribution_eq]

end

end RHTower
