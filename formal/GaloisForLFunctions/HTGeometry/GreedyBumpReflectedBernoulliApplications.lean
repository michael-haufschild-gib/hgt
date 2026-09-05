import GaloisForLFunctions.HTGeometry.ReflectionBoostPolarizationLaw
import GaloisForLFunctions.HTGeometry.GreedyBumpFactorialCumulants

/-!
# Greedy-bump cumulants for reflected Bernoulli channels

The reflected two-channel exponential family consists of complementary Bernoulli events.  The
complete void expansion from arXiv:2609.03581 makes each channel's connected correction series the
other channel's log probability.  Existing balanced-point score laws then become derivatives of
these all-order series.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Strict probability parameter for the reflected plus channel. -/
def reflectedBernoulliPlusStrictProbability (d t : ℝ) : StrictProbabilityParameter :=
  ⟨reflectedBernoulliPlusProbability d t,
    (_root_.HTGeometry.logisticVar_pos (d * t)).le,
    _root_.HTGeometry.logisticVar_lt_one (d * t)⟩

/-- Strict probability parameter for the reflected minus channel. -/
def reflectedBernoulliMinusStrictProbability (d t : ℝ) : StrictProbabilityParameter :=
  ⟨reflectedBernoulliMinusProbability d t,
    _root_.HTGeometry.one_sub_logisticVar_pos (d * t) |>.le,
    by
      rw [reflectedBernoulliMinusProbability, reflectedBernoulliPlusProbability]
      linarith [_root_.HTGeometry.logisticVar_pos (d * t)]⟩

/-- Complete connected correction series of the plus event. -/
def reflectedBernoulliPlusCumulantSeries (d t : ℝ) : ℝ :=
  ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
    (reflectedBernoulliPlusStrictProbability d t) k

/-- Complete connected correction series of the minus event. -/
def reflectedBernoulliMinusCumulantSeries (d t : ℝ) : ℝ :=
  ∑' k : ℕ, greedyBumpBernoulliLogVoidContribution
    (reflectedBernoulliMinusStrictProbability d t) k

/-- Plus-event cumulants reconstruct log probability of the complementary minus channel. -/
theorem reflectedBernoulliPlusCumulantSeries_eq_log_minus (d t : ℝ) :
    reflectedBernoulliPlusCumulantSeries d t =
      Real.log (reflectedBernoulliMinusProbability d t) := by
  have h := (greedyBumpBernoulli_logVoidSeries_hasSum
    (reflectedBernoulliPlusStrictProbability d t)).tsum_eq
  simpa [reflectedBernoulliPlusCumulantSeries,
    reflectedBernoulliPlusStrictProbability,
    reflectedBernoulliMinusProbability] using h

/-- Minus-event cumulants reconstruct log probability of the complementary plus channel. -/
theorem reflectedBernoulliMinusCumulantSeries_eq_log_plus (d t : ℝ) :
    reflectedBernoulliMinusCumulantSeries d t =
      Real.log (reflectedBernoulliPlusProbability d t) := by
  have h := (greedyBumpBernoulli_logVoidSeries_hasSum
    (reflectedBernoulliMinusStrictProbability d t)).tsum_eq
  simpa [reflectedBernoulliMinusCumulantSeries,
    reflectedBernoulliMinusStrictProbability,
    reflectedBernoulliMinusProbability] using h

/-- At balance, each channel's complete correction is `-log 2`. -/
theorem reflectedBernoulliPlusCumulantSeries_zero (d : ℝ) :
    reflectedBernoulliPlusCumulantSeries d 0 = -Real.log 2 := by
  rw [reflectedBernoulliPlusCumulantSeries_eq_log_minus,
    reflectedBernoulliMinusProbability_zero]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

/-- At balance, the complementary channel has the same complete correction. -/
theorem reflectedBernoulliMinusCumulantSeries_zero (d : ℝ) :
    reflectedBernoulliMinusCumulantSeries d 0 = -Real.log 2 := by
  rw [reflectedBernoulliMinusCumulantSeries_eq_log_plus,
    reflectedBernoulliPlusProbability_zero]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

/-- Balanced derivative of plus-event cumulants is the negative reflected rate because their void
is the minus channel. -/
theorem hasDerivAt_reflectedBernoulliPlusCumulantSeries_zero (d : ℝ) :
    HasDerivAt (reflectedBernoulliPlusCumulantSeries d) (-d) 0 := by
  have hfun : reflectedBernoulliPlusCumulantSeries d =
      fun t => Real.log (reflectedBernoulliMinusProbability d t) := by
    funext t
    exact reflectedBernoulliPlusCumulantSeries_eq_log_minus d t
  rw [hfun]
  exact hasDerivAt_log_reflectedBernoulliMinusProbability_zero d

/-- Balanced derivative of minus-event cumulants is the positive reflected rate. -/
theorem hasDerivAt_reflectedBernoulliMinusCumulantSeries_zero (d : ℝ) :
    HasDerivAt (reflectedBernoulliMinusCumulantSeries d) d 0 := by
  have hfun : reflectedBernoulliMinusCumulantSeries d =
      fun t => Real.log (reflectedBernoulliPlusProbability d t) := by
    funext t
    exact reflectedBernoulliMinusCumulantSeries_eq_log_plus d t
  rw [hfun]
  exact hasDerivAt_log_reflectedBernoulliPlusProbability_zero d

end

end GaloisForLFunctions.HTGeometry
