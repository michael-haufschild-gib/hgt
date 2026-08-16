import GaloisForLFunctions.RHTower.Sieve.InghamUniformGabrielScalarFamily

namespace RHTower.Sieve

noncomputable section

noncomputable def inghamUniformGabrielLeftWeight (sigma : ℝ) : ℝ :=
  (inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
    (inghamUniformGabrielRightEdge sigma - 1 / 2)

noncomputable def inghamUniformGabrielRightWeight (sigma : ℝ) : ℝ :=
  (inghamUniformGabrielCenter sigma - 1 / 2) /
    (inghamUniformGabrielRightEdge sigma - 1 / 2)

noncomputable def inghamUniformGabrielReciprocalPower (sigma : ℝ) : ℝ :=
  1 - (1 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma -
    (1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma

theorem inghamUniformGabrielRightEdge_gt_half
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    1 / 2 < inghamUniformGabrielRightEdge sigma := by
  unfold inghamUniformGabrielRightEdge
  nlinarith

theorem inghamUniformGabrielCenter_ge_half
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) :
    1 / 2 ≤ inghamUniformGabrielCenter sigma := by
  unfold inghamUniformGabrielCenter
  nlinarith

theorem inghamUniformGabrielCenter_le_rightEdge
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielCenter sigma ≤ inghamUniformGabrielRightEdge sigma := by
  unfold inghamUniformGabrielCenter inghamUniformGabrielRightEdge
  nlinarith

theorem inghamUniformGabrielCenter_mem_closedStrip
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    (inghamUniformGabrielCenter sigma : ℂ) ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) (inghamUniformGabrielRightEdge sigma) := by
  exact ⟨inghamUniformGabrielCenter_ge_half hsigma0,
    inghamUniformGabrielCenter_le_rightEdge hsigma1⟩

theorem inghamUniformGabriel_weights_sum
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielLeftWeight sigma +
        inghamUniformGabrielRightWeight sigma = 1 := by
  unfold inghamUniformGabrielLeftWeight
    inghamUniformGabrielRightWeight
  have hwidth : inghamUniformGabrielRightEdge sigma - 1 / 2 ≠ 0 :=
    (sub_pos.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1)).ne'
  rw [← add_div]
  rw [div_eq_one_iff_eq hwidth]
  ring

theorem inghamUniformGabrielLeftWeight_nonneg
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielLeftWeight sigma := by
  unfold inghamUniformGabrielLeftWeight
  exact div_nonneg
    (sub_nonneg.mpr (inghamUniformGabrielCenter_le_rightEdge hsigma1))
    (sub_nonneg.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1).le)

theorem inghamUniformGabrielRightWeight_nonneg
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 ≤ inghamUniformGabrielRightWeight sigma := by
  unfold inghamUniformGabrielRightWeight
  exact div_nonneg
    (sub_nonneg.mpr (inghamUniformGabrielCenter_ge_half hsigma0))
    (sub_nonneg.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1).le)

theorem inghamUniformGabrielInteriorPower_pos
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielInteriorPower sigma :=
  lt_of_lt_of_le (by norm_num) <|
    four_thirds_le_inghamUniformGabrielInteriorPower hsigma0 hsigma1

theorem inghamUniformGabrielReciprocalPower_eq
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielReciprocalPower sigma =
      1 / inghamUniformGabrielInteriorPower sigma := by
  have hwidth : inghamUniformGabrielRightEdge sigma - 1 / 2 ≠ 0 :=
    (sub_pos.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1)).ne'
  have hden := (uniformGabrielDenominator_pos hsigma1).ne'
  unfold inghamUniformGabrielReciprocalPower
    inghamUniformGabrielLeftWeight
    inghamUniformGabrielRightWeight
    inghamUniformGabrielInteriorPower
  have hp : 4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hwidth) hden
  rw [eq_div_iff hp]
  rw [show (1 - (1 / 4 : ℝ) *
        ((inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2)) -
        (1 / 2 : ℝ) *
        ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) *
      (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
        uniformGabrielDenominator sigma) =
      ((1 - (1 / 4 : ℝ) *
        ((inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2)) -
        (1 / 2 : ℝ) *
        ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) *
      (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2))) /
        uniformGabrielDenominator sigma by ring]
  rw [div_eq_one_iff_eq hden]
  rw [show (1 - (1 / 4 : ℝ) *
        ((inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2)) -
        (1 / 2 : ℝ) *
        ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) *
      (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2)) =
      4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) -
        ((inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
          (inghamUniformGabrielRightEdge sigma - 1 / 2) -
        2 * ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
          (inghamUniformGabrielRightEdge sigma - 1 / 2) by ring]
  rw [div_mul_cancel₀ _ hwidth]
  rw [show 2 * ((inghamUniformGabrielCenter sigma - 1 / 2) /
      (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
      (inghamUniformGabrielRightEdge sigma - 1 / 2) =
      2 * (((inghamUniformGabrielCenter sigma - 1 / 2) /
        (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
        (inghamUniformGabrielRightEdge sigma - 1 / 2)) by ring,
    div_mul_cancel₀ _ hwidth]
  unfold uniformGabrielDenominator
  ring

theorem inghamUniformGabrielReciprocalPower_pos
    {sigma : ℝ} (hsigma0 : 7 / 10 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    0 < inghamUniformGabrielReciprocalPower sigma := by
  rw [inghamUniformGabrielReciprocalPower_eq hsigma1]
  exact one_div_pos.mpr
    (inghamUniformGabrielInteriorPower_pos hsigma0 hsigma1)

theorem inghamUniformGabriel_left_share_identity
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielInteriorPower sigma *
        ((3 / 4 : ℝ) * inghamUniformGabrielLeftWeight sigma) =
      inghamUniformGabrielCriticalShare sigma := by
  have hwidth : inghamUniformGabrielRightEdge sigma - 1 / 2 ≠ 0 :=
    (sub_pos.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1)).ne'
  have hden := (uniformGabrielDenominator_pos hsigma1).ne'
  unfold inghamUniformGabrielInteriorPower
    inghamUniformGabrielLeftWeight
    inghamUniformGabrielCriticalShare
  change (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) *
      ((3 / 4 : ℝ) * ((inghamUniformGabrielRightEdge sigma -
        inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) =
    3 * (inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
      uniformGabrielDenominator sigma
  rw [eq_div_iff hden]
  rw [show (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) *
      ((3 / 4 : ℝ) * ((inghamUniformGabrielRightEdge sigma -
        inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) *
      uniformGabrielDenominator sigma =
    ((4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) * uniformGabrielDenominator sigma) *
      ((3 / 4 : ℝ) * ((inghamUniformGabrielRightEdge sigma -
        inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) by ring,
    div_mul_cancel₀ _ hden]
  rw [show 4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) *
      ((3 / 4 : ℝ) * ((inghamUniformGabrielRightEdge sigma -
        inghamUniformGabrielCenter sigma) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) =
    3 * (((inghamUniformGabrielRightEdge sigma - inghamUniformGabrielCenter sigma) /
      (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
        (inghamUniformGabrielRightEdge sigma - 1 / 2)) by ring,
    div_mul_cancel₀ _ hwidth]

theorem inghamUniformGabriel_right_share_identity
    {sigma : ℝ} (hsigma1 : sigma ≤ 1) :
    inghamUniformGabrielInteriorPower sigma *
        ((1 / 2 : ℝ) * inghamUniformGabrielRightWeight sigma) =
      inghamUniformGabrielRightShare sigma := by
  have hwidth : inghamUniformGabrielRightEdge sigma - 1 / 2 ≠ 0 :=
    (sub_pos.mpr (inghamUniformGabrielRightEdge_gt_half hsigma1)).ne'
  have hden := (uniformGabrielDenominator_pos hsigma1).ne'
  unfold inghamUniformGabrielInteriorPower
    inghamUniformGabrielRightWeight
    inghamUniformGabrielRightShare
  change (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) *
      ((1 / 2 : ℝ) * ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) =
    (2 * inghamUniformGabrielCenter sigma - 1) /
      uniformGabrielDenominator sigma
  rw [eq_div_iff hden]
  rw [show (4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) *
      ((1 / 2 : ℝ) * ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) *
      uniformGabrielDenominator sigma =
    ((4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) /
      uniformGabrielDenominator sigma) * uniformGabrielDenominator sigma) *
      ((1 / 2 : ℝ) * ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) by ring,
    div_mul_cancel₀ _ hden]
  rw [show 4 * (inghamUniformGabrielRightEdge sigma - 1 / 2) *
      ((1 / 2 : ℝ) * ((inghamUniformGabrielCenter sigma - 1 / 2) /
          (inghamUniformGabrielRightEdge sigma - 1 / 2))) =
    2 * (((inghamUniformGabrielCenter sigma - 1 / 2) /
      (inghamUniformGabrielRightEdge sigma - 1 / 2)) *
        (inghamUniformGabrielRightEdge sigma - 1 / 2)) by ring,
    div_mul_cancel₀ _ hwidth]
  ring

end

end RHTower.Sieve
