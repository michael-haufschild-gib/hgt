import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualQuarterGlobalSlope

noncomputable section

open Complex Set

namespace RHTower

theorem exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_central :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {tau : ℝ}, 4 ≤ tau → ∀ v : ℝ,
      2 * |v| ≤ tau →
      ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ ≤
        C * (1 + |v|) ^ 5 /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_pos_le
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  let B : ℝ := 4 + 2 * Real.pi
  let C : ℝ := 2 * K ^ 2 * B
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro tau htau v hvCentral
  have htau0 : 0 < tau := by linarith
  have htauNonneg : 0 ≤ tau := htau0.le
  let q : ℝ := 1 + |v|
  let r : ℝ := tau ^ (1 / 4 : ℝ)
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hr0 : 0 < r := by
    dsimp only [r]
    exact Real.rpow_pos_of_pos htau0 _
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_nonneg htauNonneg]
    exact max_eq_right (by linarith)
  have hqpow : q ^ (1 / 4 : ℝ) ≤ q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hr :
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * q / r := by
    have hraw := hratio tau v
    rw [hmax] at hraw
    have hstep : K * q ^ (1 / 4 : ℝ) / r ≤ K * q / r :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow hK) hr0.le
    have hquarter : (((-1 / 4 : ℝ) : ℂ)) =
        ((-(1 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hquarter]
    exact hraw.trans (by simpa only [q, r] using hstep)
  have hslope := norm_logDeriv_zetaChi_quarter_shift_sub_line_le htau hvCentral
  have h16 : 16 / tau ^ 2 ≤ 4 / tau := by
    apply (div_le_iff₀ (sq_pos_of_pos htau0)).2
    field_simp
    nlinarith
  have hslope' :
      ‖logDeriv zetaChi
          (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤ B / tau * q := by
    refine hslope.trans ?_
    dsimp only [B, q]
    calc
      (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)
          ≤ (4 / tau + 2 * Real.pi / tau) * (1 + |v|) := by gcongr
      _ = (4 + 2 * Real.pi) / tau * (1 + |v|) := by ring
  have hq3 : q ^ 3 ≤ q ^ 5 := by
    exact pow_le_pow_right₀ hq1 (by omega)
  unfold smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative
    smoothAFEZetaChiShiftQuarterHeightDerivative
  simp only [norm_mul, norm_ofNat, norm_I, one_mul]
  calc
    2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖logDeriv zetaChi
                (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
              logDeriv zetaChi (linePt tau)‖)
        ≤ 2 * (K * q / r) * ((K * q / r) * (B / tau * q)) := by gcongr
    _ = C * q ^ 3 / (tau * r ^ 2) := by
      dsimp only [C]
      ring
    _ ≤ C * q ^ 5 / (tau * r ^ 2) := by gcongr
    _ = C * (1 + |v|) ^ 5 /
        (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by rfl

theorem exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_outer :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {tau : ℝ}, 4 ≤ tau → ∀ v : ℝ,
      tau < 2 * |v| →
      ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ ≤
        C * (1 + |v|) ^ 5 /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_pos_le
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨D, hD, hslopeGlobal⟩ :=
    exists_norm_logDeriv_zetaChi_quarter_shift_sub_line_le_global
  let C : ℝ := 2 * K ^ 2 * (6 * D)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro tau htau v hvOuter
  have htau0 : 0 < tau := by linarith
  have htauNonneg : 0 ≤ tau := htau0.le
  let q : ℝ := 1 + |v|
  let r : ℝ := tau ^ (1 / 4 : ℝ)
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
  have hr0 : 0 < r := by
    dsimp only [r]
    exact Real.rpow_pos_of_pos htau0 _
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_nonneg htauNonneg]
    exact max_eq_right (by linarith)
  have hqpow : q ^ (1 / 4 : ℝ) ≤ q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hr :
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * q / r := by
    have hraw := hratio tau v
    rw [hmax] at hraw
    have hstep : K * q ^ (1 / 4 : ℝ) / r ≤ K * q / r :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow hK) hr0.le
    have hquarter : (((-1 / 4 : ℝ) : ℂ)) =
        ((-(1 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hquarter]
    exact hraw.trans (by simpa only [q, r] using hstep)
  have hslope := hslopeGlobal tau v
  rw [abs_of_nonneg htauNonneg] at hslope
  have houterFactor : 1 + tau ≤ 6 * q ^ 2 / tau := by
    apply (le_div_iff₀ htau0).2
    have htq : tau ≤ 2 * q := by
      dsimp only [q]
      linarith
    have h1tq : 1 + tau ≤ 3 * q := by
      dsimp only [q]
      linarith [abs_nonneg v]
    calc
      (1 + tau) * tau ≤ (3 * q) * (2 * q) :=
        mul_le_mul h1tq htq htauNonneg (by positivity)
      _ = 6 * q ^ 2 := by ring
  have hslope' :
      ‖logDeriv zetaChi
          (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)‖ ≤
        (6 * D / tau) * q ^ 3 := by
    refine hslope.trans ?_
    dsimp only [q]
    calc
      D * (1 + tau) * (1 + |v|)
          ≤ D * (6 * (1 + |v|) ^ 2 / tau) * (1 + |v|) := by gcongr
      _ = (6 * D / tau) * (1 + |v|) ^ 3 := by ring
  unfold smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative
    smoothAFEZetaChiShiftQuarterHeightDerivative
  simp only [norm_mul, norm_ofNat, norm_I, one_mul]
  calc
    2 * ‖smoothAFEZetaChiShiftRatio (linePt tau)
            (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
          (‖smoothAFEZetaChiShiftRatio (linePt tau)
              (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ *
            ‖logDeriv zetaChi
                (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
              logDeriv zetaChi (linePt tau)‖)
        ≤ 2 * (K * q / r) *
          ((K * q / r) * ((6 * D / tau) * q ^ 3)) := by gcongr
    _ = C * q ^ 5 / (tau * r ^ 2) := by
      dsimp only [C]
      ring
    _ = C * (1 + |v|) ^ 5 /
        (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by rfl


/-- Uniform negative-quarter squared-carrier derivative. Central conductor
cancellation and the complementary Gaussian-tail trade give the same
`tau^(-3/2)` envelope. -/
theorem exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {tau : ℝ}, 4 ≤ tau → ∀ v : ℝ,
      ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ ≤
        C * (1 + |v|) ^ 5 /
          (tau * (tau ^ (1 / 4 : ℝ)) ^ 2) := by
  obtain ⟨C₁, hC₁, hcentral⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_central
  obtain ⟨C₂, hC₂, houter⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_outer
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro tau htau v
  have htau0 : 0 < tau := by linarith
  have hden : 0 < tau * (tau ^ (1 / 4 : ℝ)) ^ 2 := by positivity
  by_cases hv : 2 * |v| ≤ tau
  · refine (hcentral htau v hv).trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂)
      (pow_nonneg (by positivity) 5)
  · have hv' : tau < 2 * |v| := lt_of_not_ge hv
    refine (houter htau v hv').trans ?_
    apply div_le_div_of_nonneg_right _ hden.le
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁)
      (pow_nonneg (by positivity) 5)

end RHTower
