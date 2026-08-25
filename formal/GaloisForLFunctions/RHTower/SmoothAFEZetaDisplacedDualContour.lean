import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContour

/-!
# Dual Gaussian residue contour at a displaced abscissa

For `s = 1/2-d+iτ`, moving the positive dual contour to
`Re w = -(d+η)` crosses only the Gaussian pole at zero.  Analyticity holds
on `Re w > -(d+1/2)`, so `η < 1/2` is the exact contour condition.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

/-- Numerator of the displaced dual Cauchy integrand. -/
def smoothAFEZetaDisplacedDualNumerator
    (d τ Y : ℝ) (w : ℂ) : ℂ :=
  smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) *
    (Y : ℂ) ^ (-w) * Complex.exp (w ^ 2)

/-- Normalized displaced dual weight on the vertical line `Re w = a`. -/
def smoothAFEZetaDisplacedDualWeightAt
    (a d τ Y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) • ∫ v : ℝ,
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ)
        (-((a : ℂ) + (v : ℂ) * I)) *
      smoothAFEMellinIntegrand Y
        ((a : ℂ) + (v : ℂ) * I)

/-- Positive-line exact dual weight based at the displaced point. -/
def smoothAFEZetaDisplacedDualWeight
    (d τ Y : ℝ) : ℂ :=
  smoothAFEZetaDisplacedDualWeightAt 1 d τ Y

theorem smoothAFEZetaDisplacedDualNumerator_zero
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) (τ Y : ℝ) :
    smoothAFEZetaDisplacedDualNumerator d τ Y 0 = 1 := by
  unfold smoothAFEZetaDisplacedDualNumerator smoothAFEZetaChiShiftRatio
  rw [neg_zero, add_zero,
    div_self (zetaChi_ne_zero_of_mem_openStrip
      (displacedLinePt_mem_openStrip hd hdhalf τ).1
      (displacedLinePt_mem_openStrip hd hdhalf τ).2)]
  norm_num

theorem smoothAFEZetaDisplacedDualNumerator_analyticOnNhd
    (d τ : ℝ) {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (smoothAFEZetaDisplacedDualNumerator d τ Y)
      {w : ℂ | -(d + 1 / 2) < w.re} := by
  let U : Set ℂ := {w : ℂ | -(d + 1 / 2) < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  haveI : NeZero (Y : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hY.ne'⟩
  apply DifferentiableOn.analyticOnNhd _ hU
  intro w hw
  have hGamma :
      Complex.Gammaℝ (1 - (displacedLinePt d τ - w)) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    rw [Complex.sub_re, Complex.one_re, Complex.sub_re,
      displacedLinePt_re]
    change -(d + 1 / 2) < w.re at hw
    linarith
  have hchi : DifferentiableAt ℂ
      (fun w : ℂ =>
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w)) w := by
    unfold smoothAFEZetaChiShiftRatio
    have hcomp := (zetaChi_analyticAt hGamma).differentiableAt.comp w
      ((differentiableAt_const (c := displacedLinePt d τ)).add
        differentiableAt_id.neg)
    simpa [Function.comp_def, sub_eq_add_neg] using
      hcomp.div_const (zetaChi (displacedLinePt d τ))
  have hpow : DifferentiableAt ℂ
      (fun w : ℂ => (Y : ℂ) ^ (-w)) w :=
    (differentiableAt_const_cpow_of_neZero (Y : ℂ) (-w)).comp w
      differentiableAt_id.neg
  have hexp : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (w ^ 2)) w :=
    Complex.differentiable_exp.differentiableAt.comp w
      (differentiableAt_id.pow 2)
  have hfun : smoothAFEZetaDisplacedDualNumerator d τ Y =
      ((fun z : ℂ =>
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-z)) *
        (fun z : ℂ => (Y : ℂ) ^ (-z))) *
        (fun z : ℂ => Complex.exp (z ^ 2)) := by
    funext z
    simp only [smoothAFEZetaDisplacedDualNumerator, Pi.mul_apply]
  rw [hfun]
  exact ((hchi.mul hpow).mul hexp).differentiableWithinAt

theorem smoothAFEZetaDisplacedDualIntegrand_eq_numerator_div
    (d τ Y : ℝ) (w : ℂ) :
    smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) *
        smoothAFEMellinIntegrand Y w =
      smoothAFEZetaDisplacedDualNumerator d τ Y w * (w - 0)⁻¹ := by
  unfold smoothAFEZetaDisplacedDualNumerator smoothAFEMellinIntegrand
  unfold smoothAFEGaussianKernel
  rw [sub_zero, div_eq_mul_inv]
  ring

/-- Finite-height residue identity for the displaced dual-weight contour. -/
theorem smoothAFEZetaDisplacedDualWeight_finite_contour
    {d η Y T : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (hη : 0 < η) (hηhalf : η < 1 / 2)
    (hY : 0 < Y) (hT : 0 < T) (τ : ℝ) :
    RHTower.rectIntegral
        (fun w : ℂ =>
          smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) *
            smoothAFEMellinIntegrand Y w)
        (((-(d + η) : ℝ) : ℂ) - (T : ℂ) * I)
        (((1 : ℝ) : ℂ) + (T : ℂ) * I) =
      2 * Real.pi * I := by
  let z₁ : ℂ := (((-(d + η) : ℝ) : ℂ) - (T : ℂ) * I)
  let z₂ : ℂ := (((1 : ℝ) : ℂ) + (T : ℂ) * I)
  let U : Set ℂ := {w : ℂ | -(d + 1 / 2) < w.re}
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro w hw
    have hwre := (Complex.mem_reProdIm.mp hw).1
    have hzre : z₁.re = -(d + η) := by simp [z₁]
    have hz2re : z₂.re = 1 := by simp [z₂]
    rw [hzre, hz2re, uIcc_of_le (by linarith)] at hwre
    have hleft : -(d + 1 / 2) < -(d + η) := by linarith
    exact hleft.trans_le hwre.1
  have hcauchy := rectIntegral_cauchyFormula_analyticOnNhd
    (g := smoothAFEZetaDisplacedDualNumerator d τ Y)
    (U := U) (p := 0) (z₁ := z₁) (z₂ := z₂)
    hsub (smoothAFEZetaDisplacedDualNumerator_analyticOnNhd d τ hY)
    (by simp [z₁]; linarith) (by simp [z₂])
    (by simp [z₁]; linarith) (by simp [z₂]; linarith)
  have hfun :
      (fun w : ℂ =>
        smoothAFEZetaDisplacedDualNumerator d τ Y w * (w - 0)⁻¹) =
      (fun w : ℂ =>
        smoothAFEZetaChiShiftRatio (displacedLinePt d τ) (-w) *
          smoothAFEMellinIntegrand Y w) := by
    funext w
    exact (smoothAFEZetaDisplacedDualIntegrand_eq_numerator_div d τ Y w).symm
  rw [hfun] at hcauchy
  rw [smoothAFEZetaDisplacedDualNumerator_zero hd hdhalf τ Y] at hcauchy
  simpa [z₁, z₂] using hcauchy

end RHTower
