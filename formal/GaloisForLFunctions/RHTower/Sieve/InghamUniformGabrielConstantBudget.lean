import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielInterpolationBudget

/-!
# Critical and right-edge shares of the uniform Gabriel interpolation

The uniform Gabriel interpolation splits a moment exponent into a critical-line share
`θ_c(σ) = 3(β_σ - c_σ)/(3β_σ - c_σ - 1)` and a right-edge share
`θ_r(σ) = (2c_σ - 1)/(3β_σ - c_σ - 1)`, where `c_σ = σ - (1 - σ)/1000` and
`β_σ = 1 + (9/100)(1 - σ)`. This module proves these shares form a convex pair.

## Main results

- `inghamUniformGabriel_shares_sum`: `θ_c(σ) + θ_r(σ) = 1` for `σ ≤ 1`.
- `inghamUniformGabrielCriticalShare_nonneg`, `inghamUniformGabrielCriticalShare_le_one`:
  `0 ≤ θ_c(σ) ≤ 1`.
- `inghamUniformGabrielRightShare_nonneg`, `inghamUniformGabrielRightShare_le_one`:
  `0 ≤ θ_r(σ) ≤ 1`.

## Hypotheses

The results are unconditional elementary identities and inequalities; they assume `σ ≤ 1`, and
`7/10 ≤ σ` where nonnegativity of the right share (hence `θ_c ≤ 1`) is needed.
-/

namespace RHTower.Sieve

noncomputable section

/-- For `σ ≤ 1`, the critical and right-edge interpolation shares sum to `1`. -/
theorem inghamUniformGabriel_shares_sum
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielCriticalShare sigma +
      inghamUniformGabrielRightShare sigma = 1 := by
  have hden :
      3 * inghamUniformGabrielRightEdge sigma -
          inghamUniformGabrielCenter sigma - 1 ≠ 0 := by
    rw [inghamUniformGabriel_denominator_eq]
    positivity
  unfold inghamUniformGabrielCriticalShare inghamUniformGabrielRightShare
  rw [← add_div, div_eq_one_iff_eq hden]
  ring

theorem inghamUniformGabrielCriticalShare_nonneg
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielCriticalShare sigma := by
  unfold inghamUniformGabrielCriticalShare
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (inghamUniformGabrielCenter_le_rightEdge hsigma1)))
    (uniformGabrielDenominator_pos hsigma1).le

theorem inghamUniformGabrielRightShare_nonneg
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielRightShare sigma := by
  unfold inghamUniformGabrielRightShare
  exact div_nonneg
    (by
      have hc := inghamUniformGabrielCenter_ge_half hsigma0
      linarith)
    (uniformGabrielDenominator_pos hsigma1).le

/-- For `7/10 ≤ σ ≤ 1`, the critical-line share is at most `1`. -/
theorem inghamUniformGabrielCriticalShare_le_one
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielCriticalShare sigma ≤ 1 := by
  rw [← inghamUniformGabriel_shares_sum hsigma1]
  exact le_add_of_nonneg_right
    (inghamUniformGabrielRightShare_nonneg hsigma0 hsigma1)

/-- For `σ ≤ 1`, the right-edge share is at most `1`. -/
theorem inghamUniformGabrielRightShare_le_one
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielRightShare sigma ≤ 1 := by
  rw [← inghamUniformGabriel_shares_sum hsigma1]
  exact le_add_of_nonneg_left
    (inghamUniformGabrielCriticalShare_nonneg hsigma1)

end

end RHTower.Sieve
