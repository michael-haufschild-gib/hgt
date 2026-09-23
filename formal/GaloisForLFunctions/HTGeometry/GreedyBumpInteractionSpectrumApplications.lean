import GaloisForLFunctions.HTGeometry.ConstitutiveInteractionSpectrumMechanics
import GaloisForLFunctions.HTGeometry.GreedyBumpBooleanGibbsApplications

/-!
# Greedy-bump cumulants in interaction-spectrum mechanics

The product interaction ledger is a Poisson-binomial point count.  Away from the exactly balanced
source cell, every activation channel is a strict one-point exclusion law.  The factorial-cumulant
hierarchy from arXiv:2609.03581 then reconstructs interaction degree mean, variance, vacuum work,
and the empty-support parity spectral weight.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite strict source, excluding the deterministic activation point `q = 1/2`. -/
structure GreedyBumpInteractionSource (I : Type*) [Fintype I] where
  bias : I → ℝ
  bias_pos : ∀ i, 0 < bias i
  bias_lt_one : ∀ i, bias i < 1
  bias_ne_half : ∀ i, bias i ≠ 1 / 2

/-- Activation probabilities form a strict Boolean source. -/
def GreedyBumpInteractionSource.activationSource
    {I : Type*} [Fintype I] (source : GreedyBumpInteractionSource I) :
    GreedyBumpBooleanSource I where
  probability i := interactionActivation (source.bias i)
  probability_nonneg i := by
    unfold interactionActivation
    exact (mul_pos (mul_pos (by norm_num) (source.bias_pos i))
      (sub_pos.mpr (source.bias_lt_one i))).le
  probability_lt_one i := by
    have hlin : 1 - 2 * source.bias i ≠ 0 := by
      intro h
      apply source.bias_ne_half i
      linarith
    have hsq : 0 < (1 - 2 * source.bias i) ^ (2 : ℕ) := sq_pos_of_ne_zero hlin
    unfold interactionActivation
    nlinarith

/-- One activation channel as a finite hard-exclusion point count. -/
def GreedyBumpInteractionSource.activationCount
    {I : Type*} [Fintype I] (source : GreedyBumpInteractionSource I) (i : I) :
    FinitePointCountLaw Bool :=
  greedyBumpBernoulliExclusion (source.activationSource.coordinate i).toProbabilityParameter

/-- Mean interaction degree is the sum of first factorial cumulants. -/
theorem GreedyBumpInteractionSource.meanDegree_eq_sum_cumulantOne
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : GreedyBumpInteractionSource I) :
    meanInteractionDegree (fun i => interactionActivation (source.bias i)) =
      ∑ i : I, (source.activationCount i).factorialCumulantOne := by
  rw [meanInteractionDegree_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [GreedyBumpInteractionSource.activationCount,
    greedyBumpBernoulli_factorialCumulantOne]
  rfl

/-- Interaction-degree variance is the sum of first plus second factorial cumulants. -/
theorem GreedyBumpInteractionSource.degreeVariance_eq_sum_cumulantOne_add_cumulantTwo
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : GreedyBumpInteractionSource I) :
    interactionDegreeVariance (fun i => interactionActivation (source.bias i)) =
      ∑ i : I, ((source.activationCount i).factorialCumulantOne +
        (source.activationCount i).factorialCumulantTwo) := by
  rw [interactionDegreeVariance_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [GreedyBumpInteractionSource.activationCount,
    greedyBumpBernoulli_factorialCumulantOne,
    greedyBumpBernoulli_factorialCumulantTwo]
  change interactionActivation (source.bias i) *
      (1 - interactionActivation (source.bias i)) =
    interactionActivation (source.bias i) - interactionActivation (source.bias i) ^ (2 : ℕ)
  ring

/-- Pair cumulants measure the exact mean--variance deficit of interaction degree. -/
theorem GreedyBumpInteractionSource.mean_sub_variance_eq_neg_sum_cumulantTwo
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : GreedyBumpInteractionSource I) :
    meanInteractionDegree (fun i => interactionActivation (source.bias i)) -
        interactionDegreeVariance (fun i => interactionActivation (source.bias i)) =
      -(∑ i : I, (source.activationCount i).factorialCumulantTwo) := by
  rw [source.meanDegree_eq_sum_cumulantOne,
    source.degreeVariance_eq_sum_cumulantOne_add_cumulantTwo]
  rw [Finset.sum_add_distrib]
  ring

/-- Complete connected correction is the log weight of the inactive interaction support. -/
theorem GreedyBumpInteractionSource.totalCumulantSeries_eq_log_emptyWork
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : GreedyBumpInteractionSource I) :
    (∑ i : I, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution (source.activationSource.coordinate i) k) =
      Real.log (interactionWorkWeight
        (fun i => interactionActivation (source.bias i)) ∅) := by
  rw [source.activationSource.totalCumulantSeries_eq_log_vacuumWeight]
  congr 1

/-- Connected interaction corrections reconstruct the empty-support parity spectral energy. -/
theorem GreedyBumpInteractionSource.totalCumulantSeries_eq_log_emptyParityEnergy
    {I : Type*} [Fintype I] [DecidableEq I]
    (source : GreedyBumpInteractionSource I) :
    (∑ i : I, ∑' k : ℕ,
      greedyBumpBernoulliLogVoidContribution (source.activationSource.coordinate i) k) =
      Real.log ((biasedWalshCoefficient source.bias biasedWalshParity ∅) ^ (2 : ℕ)) := by
  rw [source.totalCumulantSeries_eq_log_emptyWork]
  rw [← sq_biasedWalshCoefficient_parity_eq_interactionWorkWeight
    source.bias_pos source.bias_lt_one ∅]

end

end GaloisForLFunctions.HTGeometry
