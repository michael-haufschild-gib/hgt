import GaloisForLFunctions.QuantumAlg.Algorithms.Factoring.RydbergShotBudgetBridge
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump cumulants for exact retry budgets

A strict one-run failure budget is the void probability of the complementary Bernoulli success
event.  The complete void-cumulant series from arXiv:2609.03581 therefore replaces both logarithms
in the corpus's exact retry-count formula.
-/

open scoped BigOperators

noncomputable section

namespace QuantumAlg.Factoring

namespace StrictFailureBudget

open GaloisForLFunctions.HTGeometry

/-- Bernoulli success event whose void is one-run failure. -/
def successProbabilityParameter (B : StrictFailureBudget) : StrictProbabilityParameter :=
  ⟨1 - B.failureProbability, by linarith [B.failureProbability_lt_one],
    by linarith [B.failureProbability_pos]⟩

/-- Complete connected correction series of the success event is log one-run failure. -/
theorem cumulantSeries_eq_log_failureProbability (B : StrictFailureBudget) :
    (∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
      B.successProbabilityParameter k) = Real.log B.failureProbability := by
  have h := (greedyBumpBernoulli_logVoidSeries_hasSum
    B.successProbabilityParameter).tsum_eq
  simpa [successProbabilityParameter] using h

/-- Exact retry count is a ceiling of the ratio of target and one-run connected correction sums. -/
theorem exactRetryCount_eq_cumulantSeries_ceiling
    (oneRun target : StrictFailureBudget) :
    exactRetryCount oneRun target =
      ⌈(∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
          target.successProbabilityParameter k) /
        (∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
          oneRun.successProbabilityParameter k)⌉₊ := by
  rw [exactRetryCount_eq_log_ceiling,
    ← target.cumulantSeries_eq_log_failureProbability,
    ← oneRun.cumulantSeries_eq_log_failureProbability]

/-- Failure after `n` retries is the exponential of `n` copies of the connected correction sum. -/
theorem one_sub_repeatedSuccess_eq_exp_cumulantSeries
    (B : StrictFailureBudget) (n : ℕ) :
    1 - B.repeatedSuccess n =
      Real.exp ((n : ℝ) *
        (∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
          B.successProbabilityParameter k)) := by
  rw [repeatedSuccess]
  ring_nf
  rw [B.cumulantSeries_eq_log_failureProbability]
  rw [Real.exp_nat_mul]
  rw [Real.exp_log B.failureProbability_pos]

end StrictFailureBudget

end QuantumAlg.Factoring
