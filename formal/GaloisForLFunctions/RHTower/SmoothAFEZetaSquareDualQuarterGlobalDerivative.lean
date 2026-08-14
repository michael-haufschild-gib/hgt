import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualQuarterDerivativeBound

noncomputable section

open Complex Set

namespace RHTower

/-- All-height polynomial envelope used only for dominated differentiation on
the negative-quarter contour. -/
theorem exists_norm_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative_le_global :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ tau v : ℝ,
      ‖smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau v‖ ≤
        E * (1 + |tau|) * (1 + |v|) ^ 3 := by
  obtain ⟨K, hK, hratio⟩ :=
    exists_norm_smoothAFEZetaChiShiftRatio_pos_le
      (show (0 : ℝ) < 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨D, hD, hslope⟩ :=
    exists_norm_logDeriv_zetaChi_quarter_shift_sub_line_le_global
  let E : ℝ := 2 * K ^ 2 * D
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro tau v
  let q : ℝ := 1 + |v|
  have hq1 : 1 ≤ q := by dsimp only [q]; linarith [abs_nonneg v]
  have hqpow : q ^ (1 / 4 : ℝ) ≤ q := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hden : 1 ≤ (max 1 |tau|) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (le_max_left 1 |tau|) (by norm_num)
  have hr :
      ‖smoothAFEZetaChiShiftRatio (linePt tau)
          (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))‖ ≤ K * q := by
    have hraw := hratio tau v
    have hnum0 : 0 ≤ K * (1 + |v|) ^ (1 / 4 : ℝ) := by positivity
    have hdrop : K * (1 + |v|) ^ (1 / 4 : ℝ) /
        (max 1 |tau|) ^ (1 / 4 : ℝ) ≤
        K * (1 + |v|) ^ (1 / 4 : ℝ) := div_le_self hnum0 hden
    have hquarter : (((-1 / 4 : ℝ) : ℂ)) =
        ((-(1 / 4 : ℝ) : ℝ) : ℂ) := by norm_num
    rw [hquarter]
    refine hraw.trans (hdrop.trans ?_)
    dsimp only [q]
    exact mul_le_mul_of_nonneg_left hqpow hK
  have hs := hslope tau v
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
        ≤ 2 * (K * q) * ((K * q) *
          (D * (1 + |tau|) * q)) := by gcongr
    _ = E * (1 + |tau|) * q ^ 3 := by
      dsimp only [E]
      ring
    _ = E * (1 + |tau|) * (1 + |v|) ^ 3 := by rfl

/-- Negative-quarter logarithmic slope is continuous in Gaussian frequency. -/
theorem continuous_chiShiftQuarterLogSlope (tau : ℝ) :
    Continuous (fun v : ℝ =>
      logDeriv zetaChi
          (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)) := by
  have hA : Continuous (fun v : ℝ => Complex.digamma
      ((linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
          ((3 / 8 : ℝ) : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> norm_num [linePt]
    have hoff : ∀ m : ℕ,
        (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) / 2 ≠
          -(m : ℂ) := by
      rw [harg]
      exact positive_vertical_ne_neg_nat (by norm_num)
    have hinner : ContinuousAt (fun u : ℝ =>
        (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (u : ℂ) * I)) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    exact ContinuousAt.comp (x := v)
      (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
  have hC : Continuous (fun v : ℝ => Complex.digamma
      ((1 - (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro v
    have harg :
        (1 - (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
          ((1 / 8 : ℝ) : ℂ) + (((-(tau - v)) / 2 : ℝ) : ℂ) * I := by
      apply Complex.ext <;> norm_num [linePt]
    have hoff : ∀ m : ℕ,
        (1 - (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) / 2 ≠
          -(m : ℂ) := by
      rw [harg]
      exact positive_vertical_ne_neg_nat (by norm_num)
    have hinner : ContinuousAt (fun u : ℝ =>
        (1 - (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (u : ℂ) * I))) / 2) v := by
      apply ContinuousAt.div_const
      fun_prop
    exact ContinuousAt.comp (x := v)
      (GaloisForLFunctions.continuousAt_digamma _ hoff) hinner
  have heq : (fun v : ℝ =>
      logDeriv zetaChi
          (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) -
        logDeriv zetaChi (linePt tau)) = fun v : ℝ =>
      -(Complex.digamma
          ((linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) / 2) -
          Complex.digamma (linePt tau / 2)) / 2 -
        (Complex.digamma
          ((1 - (linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) / 2) -
          Complex.digamma ((1 - linePt tau) / 2)) / 2 := by
    funext v
    let z : ℂ := linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I)
    have hzpos : 0 < z.re := by dsimp only [z]; simp [linePt]; norm_num
    have h1zpos : 0 < (1 - z).re := by
      dsimp only [z]
      simp [linePt]
      norm_num
    have hspos : 0 < (linePt tau).re := by rw [linePt_re]; norm_num
    have h1spos : 0 < (1 - linePt tau).re := by
      rw [Complex.sub_re, Complex.one_re, linePt_re]
      norm_num
    rw [show linePt tau - (((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I) = z by rfl,
      logDeriv_zetaChi_off_poles
        (div_two_ne_neg_nat_of_re_pos hzpos)
        (div_two_ne_neg_nat_of_re_pos h1zpos),
      logDeriv_zetaChi_off_poles
        (div_two_ne_neg_nat_of_re_pos hspos)
        (div_two_ne_neg_nat_of_re_pos h1spos)]
    ring
  rw [heq]
  exact (((hA.sub continuous_const).neg.div_const 2).sub
    ((hC.sub continuous_const).div_const 2))

theorem continuous_smoothAFEZetaChiShiftRatio_neg_quarter (tau : ℝ) :
    Continuous (fun v : ℝ =>
      smoothAFEZetaChiShiftRatio (linePt tau)
        (-(((-1 / 4 : ℝ) : ℂ) + (v : ℂ) * I))) := by
  rw [continuous_iff_continuousAt]
  intro v
  unfold smoothAFEZetaChiShiftRatio
  apply ContinuousAt.div_const
  apply (zetaChi_analyticAt ?_).continuousAt.comp
  · fun_prop
  · apply Gammaℝ_ne_zero_of_re_pos
    simp [linePt]
    norm_num

theorem continuous_smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative
    (tau : ℝ) :
    Continuous (smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative tau) := by
  unfold smoothAFEZetaChiShiftRatioSqQuarterHeightDerivative
    smoothAFEZetaChiShiftQuarterHeightDerivative
  exact ((continuous_const.mul
    (continuous_smoothAFEZetaChiShiftRatio_neg_quarter tau)).mul
      ((continuous_const.mul
        (continuous_smoothAFEZetaChiShiftRatio_neg_quarter tau)).mul
          (continuous_chiShiftQuarterLogSlope tau)))

end RHTower
