import GaloisForLFunctions.RHTower.WeilLogShiftWeightedGenericity
import GaloisForLFunctions.RHTower.WeilLogShiftExponentialPrecision

/-!
# Generic failure at arbitrary observation precision

Every strictly positive precision profile supports generic unboundedness
and signed nonsummability, while any prescribed finite prefix stays exact.
The topology is the supremum topology on the closed unit ball of error
parameters. For the original exponential family, every nonnegative decay
rate is allowed; no upper bound on that rate remains.
-/

open Filter Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- A bounded envelope below a positive precision profile, zero on the
prescribed prefix and strictly positive at every subsequent coordinate. -/
def weilLogShiftPrefixEnvelope (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun j => if j < M then 0 else min 1 (ε j)) continuous_of_discreteTopology 1 (fun j => by
      rw [Real.norm_eq_abs]
      split_ifs
      · norm_num
      · rw [abs_of_pos (lt_min (by norm_num) (hε j))]
        exact min_le_left _ _)

theorem weilLogShiftPrefixEnvelope_apply (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M j : ℕ) :
    weilLogShiftPrefixEnvelope ε hε M j = if j < M then 0 else min 1 (ε j) := rfl

theorem weilLogShiftPrefixEnvelope_zero (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (M j : ℕ) (hj : j < M) : weilLogShiftPrefixEnvelope ε hε M j = 0 := by
  rw [weilLogShiftPrefixEnvelope_apply, if_pos hj]

theorem weilLogShiftPrefixEnvelope_pos (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (M j : ℕ) (hj : M ≤ j) : 0 < weilLogShiftPrefixEnvelope ε hε M j := by
  rw [weilLogShiftPrefixEnvelope_apply, if_neg (by omega)]
  exact lt_min (by norm_num) (hε j)

theorem weilLogShiftPrefixEnvelope_bounds (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (M j : ℕ) : 0 ≤ weilLogShiftPrefixEnvelope ε hε M j ∧
      weilLogShiftPrefixEnvelope ε hε M j ≤ ε j := by
  by_cases hj : j < M
  · rw [weilLogShiftPrefixEnvelope_zero ε hε M j hj]
    exact ⟨le_rfl, (hε j).le⟩
  · exact ⟨(weilLogShiftPrefixEnvelope_pos ε hε M j (by omega)).le,
      by rw [weilLogShiftPrefixEnvelope_apply, if_neg hj]; exact min_le_right _ _⟩

/-- Parameterized perturbations respecting arbitrary positive precision
and an exact finite prefix. -/
def weilLogShiftArbitraryPrecisionPerturbation (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) (u : ℕ →ᵇ ℝ) : ℕ →ᵇ ℝ :=
  weilLogShiftWeightedPerturbation center (weilLogShiftPrefixEnvelope ε hε M) u

/-- Every parameter in the closed unit ball satisfies the requested
coordinatewise error bounds. -/
theorem weilLogShiftArbitraryPrecisionPerturbation_bound (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ)
    (u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) (j : ℕ) :
    |weilLogShiftArbitraryPrecisionPerturbation center ε hε M u j - center j| ≤ ε j := by
  have hunorm : ‖(u : ℕ →ᵇ ℝ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
  have hu : |(u : ℕ →ᵇ ℝ) j| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using ((u : ℕ →ᵇ ℝ).norm_coe_le_norm j).trans hunorm
  obtain ⟨hq0, hqε⟩ := weilLogShiftPrefixEnvelope_bounds ε hε M j
  rw [weilLogShiftArbitraryPrecisionPerturbation, weilLogShiftWeightedPerturbation_apply,
    add_sub_cancel_left, abs_mul, abs_of_nonneg hq0]
  calc
    weilLogShiftPrefixEnvelope ε hε M j * |(u : ℕ →ᵇ ℝ) j| ≤
        weilLogShiftPrefixEnvelope ε hε M j * 1 := mul_le_mul_of_nonneg_left hu hq0
    _ ≤ ε j := by simpa only [mul_one] using hqε

/-- Every parameter preserves the entire prescribed finite prefix. -/
theorem weilLogShiftArbitraryPrecisionPerturbation_prefix (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) (u : ℕ →ᵇ ℝ) (j : ℕ) (hj : j < M) :
    weilLogShiftArbitraryPrecisionPerturbation center ε hε M u j = center j := by
  rw [weilLogShiftArbitraryPrecisionPerturbation, weilLogShiftWeightedPerturbation_apply,
    weilLogShiftPrefixEnvelope_zero ε hε M j hj, zero_mul, add_zero]

/-- Arbitrarily precise observations, with any finite exact prefix, still
have a dense residual set of error parameters whose moments are unbounded
in every tail at every real shift. -/
theorem weilLogShiftArbitraryPrecision_dense_residual_nowhere_bounded (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      WeilLogShiftUniformNowhereBounded
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u)} ∧
    {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      WeilLogShiftUniformNowhereBounded
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u)} ∈
      residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_bounded
  exact hK center (weilLogShiftPrefixEnvelope ε hε M)
    ⟨max K M, le_max_left _ _,
      ne_of_gt (weilLogShiftPrefixEnvelope_pos ε hε M (max K M) (le_max_right _ _))⟩

/-- Generic failure concerns signed summability, not only absolute summability. -/
theorem weilLogShiftArbitraryPrecision_dense_residual_nowhere_summable (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u))} ∧
    {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u))} ∈
      residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_summable
  exact hK center (weilLogShiftPrefixEnvelope ε hε M)
    ⟨max K M, le_max_left _ _,
      ne_of_gt (weilLogShiftPrefixEnvelope_pos ε hε M (max K M) (le_max_right _ _))⟩

/-- Eventual boundedness or summability at even one shift is meagre under
every positive precision profile with any finite exact prefix. -/
theorem weilLogShiftArbitraryPrecision_meagre_exceptions (center : ℕ →ᵇ ℝ)
    (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) (M : ℕ) :
    IsMeagre {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∃ (y B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n → ‖weilLogShiftRecoveryMoment y
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u) n‖ ≤ B} ∧
    IsMeagre {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∃ y : ℝ, Summable (weilLogShiftRecoveryMoment y
        (weilLogShiftArbitraryPrecisionPerturbation center ε hε M u))} := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_meagre_exceptions
  exact hK center (weilLogShiftPrefixEnvelope ε hε M)
    ⟨max K M, le_max_left _ _,
      ne_of_gt (weilLogShiftPrefixEnvelope_pos ε hε M (max K M) (le_max_right _ _))⟩

/-- Exact identification with the original exponential family; no change
of parameters or topology is used for the all-rate corollaries. -/
theorem weilLogShiftExponentialPerturbation_eq_weighted (center : ℕ →ᵇ ℝ)
    (ε σ : ℝ) (hσ : 0 ≤ σ) (u : ℕ →ᵇ ℝ) :
    weilLogShiftExponentialPerturbation center ε σ hσ u =
      weilLogShiftWeightedPerturbation center (ε • weilLogShiftExponentialEnvelope σ hσ) u := by
  ext j
  change center j + ε * (weilLogShiftExponentialEnvelope σ hσ j * u j) =
    center j + (ε * weilLogShiftExponentialEnvelope σ hσ j) * u j
  ring

/-- The original exponential family is generically nowhere bounded at
every nonnegative decay rate, without the former subcritical rate bound. -/
theorem weilLogShiftExponential_all_rates_dense_residual_nowhere_bounded (center : ℕ →ᵇ ℝ)
    (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) :
    Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      WeilLogShiftUniformNowhereBounded (weilLogShiftExponentialPerturbation center ε σ hσ u)} ∧
    {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      WeilLogShiftUniformNowhereBounded (weilLogShiftExponentialPerturbation center ε σ hσ u)} ∈
      residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_bounded
  have hq : ∃ k : ℕ, K ≤ k ∧ (ε • weilLogShiftExponentialEnvelope σ hσ) k ≠ 0 := by
    refine ⟨K, le_rfl, ?_⟩
    change ε * exp (-(σ * (K + 2 : ℕ))) ≠ 0
    exact ne_of_gt (mul_pos hε (exp_pos _))
  simpa only [weilLogShiftExponentialPerturbation_eq_weighted] using
    hK center (ε • weilLogShiftExponentialEnvelope σ hσ) hq

/-- Signed nonsummability is generic in the original exponential family
at every nonnegative decay rate. -/
theorem weilLogShiftExponential_all_rates_dense_residual_nowhere_summable (center : ℕ →ᵇ ℝ)
    (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) :
    Dense {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y
        (weilLogShiftExponentialPerturbation center ε σ hσ u))} ∧
    {u : WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1 |
      ∀ y : ℝ, ¬ Summable (weilLogShiftRecoveryMoment y
        (weilLogShiftExponentialPerturbation center ε σ hσ u))} ∈
      residual (WeilLogShiftUniformHistoryBall (0 : ℕ →ᵇ ℝ) 1) := by
  obtain ⟨K, hK⟩ := exists_weilLogShiftWeighted_dense_residual_nowhere_summable
  have hq : ∃ k : ℕ, K ≤ k ∧ (ε • weilLogShiftExponentialEnvelope σ hσ) k ≠ 0 := by
    refine ⟨K, le_rfl, ?_⟩
    change ε * exp (-(σ * (K + 2 : ℕ))) ≠ 0
    exact ne_of_gt (mul_pos hε (exp_pos _))
  simpa only [weilLogShiftExponentialPerturbation_eq_weighted] using
    hK center (ε • weilLogShiftExponentialEnvelope σ hσ) hq

end RHTower
