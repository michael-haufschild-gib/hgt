import GaloisForLFunctions.RHTower.SmoothAFEZetaChiRightBound
import GaloisForLFunctions.RHTower.RectangleCauchyFormulaOn

/-!
# Residue contour for the exact dual Gaussian weight

For `0 < δ < 1/2`, the shifted factor `χ(1/2+iτ-w)` is analytic throughout
`Re w > -1/2`.  Moving the exact dual weight from `Re w = 1` to
`Re w = -δ` therefore crosses only the Gaussian kernel pole at zero, with
unit normalized residue.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

def smoothAFEZetaDualNumerator (τ Y : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio (linePt τ) (-w) *
    (Y : ℂ) ^ (-w) * Complex.exp (w ^ 2)

def smoothAFEZetaDualWeightAt (a τ Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (linePt τ)
        (-((a : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        ((a : ℂ) + (v : ℂ) * I)

theorem smoothAFEZetaDualWeight_eq_at_one (τ Y : ℝ) :
    smoothAFEZetaDualWeight τ Y =
      smoothAFEZetaDualWeightAt 1 τ Y := by
  rfl

theorem smoothAFEZetaDualNumerator_zero
    (τ Y : ℝ) :
    smoothAFEZetaDualNumerator τ Y 0 = 1 := by
  unfold smoothAFEZetaDualNumerator smoothAFEZetaChiShiftRatio
  rw [neg_zero, add_zero, div_self (zetaChi_line_ne_zero τ)]
  norm_num

theorem smoothAFEZetaDualNumerator_analyticOnNhd
    (τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (smoothAFEZetaDualNumerator τ Y)
      {w : ℂ | -1 / 2 < w.re} := by
  let U : Set ℂ := {w : ℂ | -1 / 2 < w.re}
  have hU : IsOpen U :=
    isOpen_lt continuous_const Complex.continuous_re
  haveI : NeZero (Y : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  apply DifferentiableOn.analyticOnNhd _ hU
  intro w hw
  have hGamma :
      Complex.Gammaℝ (1 - (linePt τ - w)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re, Complex.sub_re, linePt_re]
    change -1 / 2 < w.re at hw
    linarith
  have hchi :
      DifferentiableAt ℂ
        (fun w : ℂ => smoothAFEZetaChiShiftRatio (linePt τ) (-w)) w := by
    unfold smoothAFEZetaChiShiftRatio
    have hcomp := (zetaChi_analyticAt hGamma).differentiableAt.comp w
      ((differentiableAt_const (c := linePt τ)).add
        differentiableAt_id.neg)
    simpa [Function.comp_def, sub_eq_add_neg] using
      hcomp.div_const (zetaChi (linePt τ))
  have hpow :
      DifferentiableAt ℂ (fun w : ℂ => (Y : ℂ) ^ (-w)) w :=
    (differentiableAt_const_cpow_of_neZero (Y : ℂ) (-w)).comp w
      differentiableAt_id.neg
  have hexp :
      DifferentiableAt ℂ (fun w : ℂ => Complex.exp (w ^ 2)) w :=
    Complex.differentiable_exp.differentiableAt.comp w
      (differentiableAt_id.pow 2)
  simpa [smoothAFEZetaDualNumerator] using
    ((hchi.mul hpow).mul hexp).differentiableWithinAt

theorem smoothAFEZetaDualIntegrand_eq_numerator_div
    (τ Y : ℝ) (w : ℂ) :
    smoothAFEZetaChiShiftRatio (linePt τ) (-w) *
        smoothAFEMellinIntegrand Y w =
      smoothAFEZetaDualNumerator τ Y w * (w - 0)⁻¹ := by
  unfold smoothAFEZetaDualNumerator smoothAFEMellinIntegrand
  unfold smoothAFEGaussianKernel
  rw [sub_zero, div_eq_mul_inv]
  ring

/-- Finite-height residue identity for the dual-weight contour. -/
theorem smoothAFEZetaDualWeight_finite_contour
    {δ Y T : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hY : 0 < Y) (hT : 0 < T) (τ : ℝ) :
    RHTower.rectIntegral
        (fun w : ℂ =>
          smoothAFEZetaChiShiftRatio (linePt τ) (-w) *
            smoothAFEMellinIntegrand Y w)
        (((-δ : ℝ) : ℂ) - (T : ℂ) * I)
        (((1 : ℝ) : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I := by
  let z₁ : ℂ := (((-δ : ℝ) : ℂ) - (T : ℂ) * I)
  let z₂ : ℂ := (((1 : ℝ) : ℂ) + (T : ℂ) * I)
  let U : Set ℂ := {w : ℂ | -1 / 2 < w.re}
  have hsub :
      (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    have hzre : z₁.re = -δ := by simp [z₁]
    have hz2re : z₂.re = 1 := by simp [z₂]
    rw [hzre, hz2re, uIcc_of_le (by linarith)] at hwre
    have hleft : -1 / 2 < -δ := by linarith
    exact hleft.trans_le hwre.1
  have hcauchy :=
    rectIntegral_cauchyFormula_analyticOnNhd
      (g := smoothAFEZetaDualNumerator τ Y)
      (U := U) (p := 0) (z₁ := z₁) (z₂ := z₂)
      hsub (smoothAFEZetaDualNumerator_analyticOnNhd τ hY)
      (by simp [z₁]; linarith) (by simp [z₂])
      (by simp [z₁]; linarith) (by simp [z₂]; linarith)
  have hfun :
      (fun w : ℂ =>
        smoothAFEZetaDualNumerator τ Y w * (w - 0)⁻¹) =
      (fun w : ℂ =>
        smoothAFEZetaChiShiftRatio (linePt τ) (-w) *
          smoothAFEMellinIntegrand Y w) := by
    funext w
    exact (smoothAFEZetaDualIntegrand_eq_numerator_div τ Y w).symm
  rw [hfun] at hcauchy
  rw [smoothAFEZetaDualNumerator_zero τ Y] at hcauchy
  simpa [z₁, z₂] using hcauchy

end RHTower
