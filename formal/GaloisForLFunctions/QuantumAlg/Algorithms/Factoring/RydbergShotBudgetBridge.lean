import GaloisForLFunctions.HTGeometry.RydbergShotSuccessLaw
import GaloisForLFunctions.QuantumAlg.Algorithms.Factoring.ShorStyle

/-!
# Exact logarithmic retry bridge

The exact shot-count theorem extracted from arXiv:2608.29858 is applied to the
existing Shor-style rational failure-budget vocabulary.  Strict failure budgets
are packaged as data, eliminating side-condition premises from exported laws.
-/

noncomputable section

namespace QuantumAlg.Factoring

/-- Rational failure budget strictly between zero and one. -/
structure StrictFailureBudget where
  budget : FailureBudget
  numerator_pos : 0 < budget.failureNumerator
  numerator_lt_denominator :
    budget.failureNumerator < budget.failureDenominator

namespace StrictFailureBudget

def failureProbability (B : StrictFailureBudget) : ℝ :=
  (B.budget.failureNumerator : ℝ) / B.budget.failureDenominator

theorem failureProbability_pos (B : StrictFailureBudget) :
    0 < B.failureProbability := by
  unfold failureProbability
  apply div_pos
  · exact_mod_cast B.numerator_pos
  · exact_mod_cast Nat.zero_lt_of_lt B.numerator_lt_denominator

theorem failureProbability_lt_one (B : StrictFailureBudget) :
    B.failureProbability < 1 := by
  rw [failureProbability, div_lt_one]
  · exact_mod_cast B.numerator_lt_denominator
  · exact_mod_cast Nat.zero_lt_of_lt B.numerator_lt_denominator

theorem wellFormed (B : StrictFailureBudget) : B.budget.WellFormed := by
  exact ⟨Nat.zero_lt_of_lt B.numerator_lt_denominator,
    B.numerator_lt_denominator.le⟩

/-- Convert one-run and target failure budgets into the certified shot problem. -/
def shotTarget (oneRun target : StrictFailureBudget) : HTGeometry.RydbergShotTarget where
  oneShotSuccess := 1 - oneRun.failureProbability
  confidence := 1 - target.failureProbability
  oneShotSuccess_pos := by linarith [oneRun.failureProbability_lt_one]
  oneShotSuccess_lt_one := by linarith [oneRun.failureProbability_pos]
  confidence_pos := by linarith [target.failureProbability_lt_one]
  confidence_lt_one := by linarith [target.failureProbability_pos]

/-- Existing rational repeated-trial success field, interpreted in `ℝ`. -/
def repeatedSuccess (oneRun : StrictFailureBudget) (n : ℕ) : ℝ :=
  1 - oneRun.failureProbability ^ n

def requestedConfidence (target : StrictFailureBudget) : ℝ :=
  1 - target.failureProbability

/-- Exact least retry count for the two rational failure budgets. -/
def exactRetryCount (oneRun target : StrictFailureBudget) : ℕ :=
  (shotTarget oneRun target).integerShotBudget

theorem exactRetryCount_eq_log_ceiling (oneRun target : StrictFailureBudget) :
    exactRetryCount oneRun target =
      ⌈Real.log target.failureProbability /
        Real.log oneRun.failureProbability⌉₊ := by
  simp [exactRetryCount, HTGeometry.RydbergShotTarget.integerShotBudget,
    HTGeometry.RydbergShotTarget.continuousShotBudget,
    HTGeometry.RydbergShotTarget.targetFailure,
    HTGeometry.RydbergShotTarget.failureBase, shotTarget]

/-- The logarithmic ceiling is not merely sufficient: it is the least natural
retry count meeting the existing rational confidence target. -/
theorem exactRetryCount_isLeast (oneRun target : StrictFailureBudget) :
    IsLeast
      {n : ℕ | target.requestedConfidence ≤ oneRun.repeatedSuccess n}
      (exactRetryCount oneRun target) := by
  simpa [exactRetryCount, shotTarget, requestedConfidence, repeatedSuccess,
    HTGeometry.RydbergShotTarget.successAfter,
    HTGeometry.RydbergShotTarget.failureAfter,
    HTGeometry.RydbergShotTarget.failureBase] using
      (shotTarget oneRun target).integerShotBudget_isLeast

end StrictFailureBudget

end QuantumAlg.Factoring
