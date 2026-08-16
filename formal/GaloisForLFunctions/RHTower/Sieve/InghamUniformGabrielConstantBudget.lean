import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielInterpolationBudget

namespace RHTower.Sieve

noncomputable section

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

theorem inghamUniformGabrielCriticalShare_le_one
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielCriticalShare sigma ≤ 1 := by
  rw [← inghamUniformGabriel_shares_sum hsigma1]
  exact le_add_of_nonneg_right
    (inghamUniformGabrielRightShare_nonneg hsigma0 hsigma1)

theorem inghamUniformGabrielRightShare_le_one
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielRightShare sigma ≤ 1 := by
  rw [← inghamUniformGabriel_shares_sum hsigma1]
  exact le_add_of_nonneg_left
    (inghamUniformGabrielCriticalShare_nonneg hsigma1)

end

end RHTower.Sieve
