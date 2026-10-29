import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1XiCoefficients
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalBoundary
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# Exponential growth bound for affine A₁ ξ coefficients

The entire completion has a contractive unit-shift quotient. Restoring its
polynomial normalization bounds Garland's meromorphic ξ quotient on every
closed sub-half-plane of `Re s > 1`. Products grow at most exponentially in
the exact affine Weyl inversion count.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

noncomputable section

private theorem re_gt_one_ne_one {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro he
  have h := congrArg Complex.re he
  simp only [Complex.one_re] at h
  linarith only [hs, h]

private theorem xiRatio_eq_entireRatio {s : ℂ} (hs : 1 < s.re) :
    xiRatio s = (s + 1) / (s - 1) * (RHTower.xi s / RHTower.xi (s + 1)) := by
  have hs' : 1 < (s + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hs]
  rw [RHTower.xi_eq_mul_completedRiemannZeta (Complex.ne_zero_of_one_lt_re hs) (re_gt_one_ne_one hs),
    RHTower.xi_eq_mul_completedRiemannZeta (Complex.ne_zero_of_one_lt_re hs') (re_gt_one_ne_one hs')]
  unfold xiRatio
  field_simp [Complex.ne_zero_of_one_lt_re hs, sub_ne_zero.mpr (re_gt_one_ne_one hs),
    Complex.ne_zero_of_one_lt_re hs', completedZeta_ne_zero_right hs']
  ring

private theorem norm_entireRatio_le_one {s : ℂ} (hs : 1 < s.re) :
    ‖RHTower.xi s / RHTower.xi (s + 1)‖ ≤ 1 := by
  have hz : -1 ≤ (s - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hs]
  have h := RHTower.SelbergThetaHorizontalBoundary.norm_scatteringCore_le hz
  simpa only [RHTower.SelbergThetaHorizontalBoundary.scatteringCore, sub_add_cancel,
    show s - 1 + 2 = s + 1 by ring] using h

private theorem norm_xiRatio_le_margin {s : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hs : 1 + δ ≤ s.re) : ‖xiRatio s‖ ≤ 1 + 2 / δ := by
  have hs' : 1 < s.re := lt_of_lt_of_le (lt_add_of_pos_right 1 hδ) hs
  have hnorm : δ ≤ ‖s - 1‖ := by
    calc
      δ ≤ (s - 1).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith only [hs]
      _ ≤ ‖s - 1‖ := Complex.re_le_norm _
  have hnormpos : 0 < ‖s - 1‖ := lt_of_lt_of_le hδ hnorm
  have htriangle : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
    have h := norm_add_le (s - 1) (2 : ℂ)
    rw [show s - 1 + 2 = s + 1 by ring] at h
    simpa only [Complex.norm_ofNat] using h
  calc
    ‖xiRatio s‖ = ‖(s + 1) / (s - 1)‖ * ‖RHTower.xi s / RHTower.xi (s + 1)‖ := by
      rw [xiRatio_eq_entireRatio hs', norm_mul]
    _ ≤ ‖(s + 1) / (s - 1)‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_entireRatio_le_one hs') (norm_nonneg _)
    _ = ‖s + 1‖ / ‖s - 1‖ := by rw [mul_one, norm_div]
    _ ≤ (‖s - 1‖ + 2) / ‖s - 1‖ :=
      div_le_div_of_nonneg_right htriangle hnormpos.le
    _ = 1 + 2 / ‖s - 1‖ := by rw [add_div, div_self hnormpos.ne']
    _ ≤ 1 + 2 / δ := by
      have hdiv : (2 : ℝ) / ‖s - 1‖ ≤ 2 / δ :=
        div_le_div_of_nonneg_left (by positivity) hδ hnorm
      linarith only [hdiv]

/-- Distance of the closest simple-coroot parameter from the line `Re s = 1`. -/
def chamberMargin (p : ℂ × ℂ) : ℝ :=
  min (chamberCoordinate p.1).re (chamberCoordinate p.2).re - 1

theorem chamberMargin_pos (p : ℂ × ℂ) : 0 < chamberMargin p := by
  exact sub_pos.mpr
    (lt_min (chamberCoordinate_re_gt_one p.1) (chamberCoordinate_re_gt_one p.2))

/-- A uniform exponential rate for every root factor in the chamber. -/
def coefficientRate (p : ℂ × ℂ) : ℝ := 2 / chamberMargin p

theorem coefficientRate_pos (p : ℂ × ℂ) : 0 < coefficientRate p := by
  exact div_pos (by positivity) (chamberMargin_pos p)

theorem root_xiRatio_norm_le_exp (p : ℂ × ℂ) (w : Weyl) :
    ∀ β ∈ inversions w,
      ‖xiRatio (rootArgument (godementParameter p) β)‖ ≤ Real.exp (coefficientRate p) := by
  intro β hβ
  have hs : 1 + chamberMargin p ≤ (rootArgument (godementParameter p) β).re := by
    have h := rootArgument_re_ge_min p w β hβ
    unfold chamberMargin
    linarith only [h]
  calc
    ‖xiRatio (rootArgument (godementParameter p) β)‖ ≤ 1 + coefficientRate p :=
      norm_xiRatio_le_margin (chamberMargin_pos p) hs
    _ ≤ Real.exp (coefficientRate p) := by
      simpa only [add_comm] using Real.add_one_le_exp (coefficientRate p)

/-- The ξ coefficient grows at most exponentially in the exact inversion count. -/
theorem xiCoefficient_norm_le_exp (p : ℂ × ℂ) (w : Weyl) :
    ‖xiCoefficient (godementParameter p) w‖ ≤
      Real.exp ((inversions w).card * coefficientRate p) := by
  calc
    ‖xiCoefficient (godementParameter p) w‖ ≤
        ∏ β ∈ inversions w, ‖xiRatio (rootArgument (godementParameter p) β)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _β ∈ inversions w, Real.exp (coefficientRate p) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (root_xiRatio_norm_le_exp p w)
    _ = Real.exp ((inversions w).card * coefficientRate p) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]

/-- Sharp translation length in the exponential coefficient bound. -/
theorem xiCoefficient_translation_norm_le (p : ℂ × ℂ) (m : ℤ) :
    ‖xiCoefficient (godementParameter p) (.r m)‖ ≤
      Real.exp ((2 * m).natAbs * coefficientRate p) := by
  simpa only [inversions_translation_card] using xiCoefficient_norm_le_exp p (.r m)

/-- Sharp reflection length in the exponential coefficient bound. -/
theorem xiCoefficient_reflection_norm_le (p : ℂ × ℂ) (m : ℤ) :
    ‖xiCoefficient (godementParameter p) (.sr m)‖ ≤
      Real.exp ((2 * m + 1).natAbs * coefficientRate p) := by
  simpa only [inversions_reflection_card] using xiCoefficient_norm_le_exp p (.sr m)

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
