import Mathlib

/-!
# Exact shot-to-success law

The logarithmic repetition count used in arXiv:2608.29858 is formalized without
asymptotics.  A `RydbergShotTarget` packages the probability side conditions, so
all exported results are closed consequences of the certified target itself.
-/

namespace HTGeometry

/-- Certified one-shot success probability and requested confidence. -/
structure RydbergShotTarget where
  oneShotSuccess : ℝ
  confidence : ℝ
  oneShotSuccess_pos : 0 < oneShotSuccess
  oneShotSuccess_lt_one : oneShotSuccess < 1
  confidence_pos : 0 < confidence
  confidence_lt_one : confidence < 1

namespace RydbergShotTarget

/-- Probability that one independent shot fails. -/
def failureBase (T : RydbergShotTarget) : ℝ :=
  1 - T.oneShotSuccess

/-- Maximum failure probability compatible with the requested confidence. -/
def targetFailure (T : RydbergShotTarget) : ℝ :=
  1 - T.confidence

/-- Real-valued threshold appearing before rounding to a natural shot count. -/
noncomputable def continuousShotBudget (T : RydbergShotTarget) : ℝ :=
  Real.log T.targetFailure / Real.log T.failureBase

/-- Least natural shot count above the exact logarithmic threshold. -/
noncomputable def integerShotBudget (T : RydbergShotTarget) : ℕ :=
  ⌈T.continuousShotBudget⌉₊

/-- Failure probability after `n` independent shots. -/
def failureAfter (T : RydbergShotTarget) (n : ℕ) : ℝ :=
  T.failureBase ^ n

/-- Probability of seeing at least one success in `n` independent shots. -/
def successAfter (T : RydbergShotTarget) (n : ℕ) : ℝ :=
  1 - T.failureAfter n

theorem failureBase_pos (T : RydbergShotTarget) : 0 < T.failureBase := by
  unfold failureBase
  linarith [T.oneShotSuccess_lt_one]

theorem failureBase_lt_one (T : RydbergShotTarget) : T.failureBase < 1 := by
  unfold failureBase
  linarith [T.oneShotSuccess_pos]

theorem targetFailure_pos (T : RydbergShotTarget) : 0 < T.targetFailure := by
  unfold targetFailure
  linarith [T.confidence_lt_one]

theorem targetFailure_lt_one (T : RydbergShotTarget) : T.targetFailure < 1 := by
  unfold targetFailure
  linarith [T.confidence_pos]

theorem continuousShotBudget_pos (T : RydbergShotTarget) :
    0 < T.continuousShotBudget := by
  exact div_pos_of_neg_of_neg
    (Real.log_neg T.targetFailure_pos T.targetFailure_lt_one)
    (Real.log_neg T.failureBase_pos T.failureBase_lt_one)

/-- The logarithmic threshold has exactly the requested residual failure. -/
theorem failure_rpow_continuousShotBudget_eq (T : RydbergShotTarget) :
    T.failureBase ^ T.continuousShotBudget = T.targetFailure := by
  rw [Real.rpow_def_of_pos T.failureBase_pos]
  have hlog : Real.log T.failureBase ≠ 0 :=
    ne_of_lt (Real.log_neg T.failureBase_pos T.failureBase_lt_one)
  have hcancel :
      Real.log T.failureBase * T.continuousShotBudget = Real.log T.targetFailure := by
    unfold continuousShotBudget
    field_simp
  rw [hcancel, Real.exp_log T.targetFailure_pos]

/-- Before integer rounding, the formula reaches the confidence exactly. -/
theorem continuousShotBudget_exact (T : RydbergShotTarget) :
    1 - T.failureBase ^ T.continuousShotBudget = T.confidence := by
  rw [T.failure_rpow_continuousShotBudget_eq]
  unfold targetFailure
  ring

/-- The rounded number of shots reaches at least the requested confidence. -/
theorem integerShotBudget_sufficient (T : RydbergShotTarget) :
    T.confidence ≤ T.successAfter T.integerShotBudget := by
  have hfailure :
      T.failureAfter T.integerShotBudget ≤ T.targetFailure := by
    unfold failureAfter integerShotBudget
    rw [← Real.rpow_natCast]
    calc
      T.failureBase ^ (↑⌈T.continuousShotBudget⌉₊ : ℝ) ≤
          T.failureBase ^ T.continuousShotBudget :=
        Real.rpow_le_rpow_of_exponent_ge T.failureBase_pos
          (le_of_lt T.failureBase_lt_one) (Nat.le_ceil T.continuousShotBudget)
      _ = T.targetFailure := T.failure_rpow_continuousShotBudget_eq
  unfold successAfter
  unfold targetFailure at hfailure
  linarith

/-- Every smaller natural shot count fails to reach the requested confidence. -/
theorem integerShotBudget_minimal (T : RydbergShotTarget) (n : Fin T.integerShotBudget) :
    T.successAfter n < T.confidence := by
  have hn : (n : ℝ) < T.continuousShotBudget := by
    exact (Nat.lt_ceil.mp n.isLt)
  have hfailure : T.targetFailure < T.failureAfter n := by
    unfold failureAfter
    rw [← Real.rpow_natCast]
    rw [← T.failure_rpow_continuousShotBudget_eq]
    exact Real.rpow_lt_rpow_of_exponent_gt T.failureBase_pos T.failureBase_lt_one hn
  unfold successAfter targetFailure at *
  linarith

/-- Exact characterization: the ceiling formula is the least sufficient count. -/
theorem integerShotBudget_isLeast (T : RydbergShotTarget) :
    IsLeast {n : ℕ | T.confidence ≤ T.successAfter n} T.integerShotBudget := by
  refine ⟨T.integerShotBudget_sufficient, ?_⟩
  intro n hn
  by_contra hnot
  have hlt : n < T.integerShotBudget := Nat.lt_of_not_ge hnot
  have hfail := T.integerShotBudget_minimal ⟨n, hlt⟩
  exact (not_lt_of_ge hn) hfail

end RydbergShotTarget

end HTGeometry
