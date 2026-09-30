import GaloisForLFunctions.RHTower.HalfGaussTransformWindowEstimates
import GaloisForLFunctions.RHTower.XiHorizontalStripComparison
import GaloisForLFunctions.HTGeometry.LogLinearGronwallModel

/-!
# `ξ` along a horizontal line as input for the one-sided Gaussian average

Put `F(w) = ξ(½ + w + iX)`. This module supplies the hypotheses of the window estimates:

* `F` is differentiable with continuous derivative `F'(w) = ξ'(½ + w + iX)`, and
  `e^{−w²/(16t)} ‖F(w)‖` is integrable (Gaussian average at heat time `4t`);
* on the window `9/2 ≤ w ≤ X/32 − 1/2` (so `5 ≤ Re s ≤ X/32`), `‖F' − aF‖ ≤ ‖F‖/8` with
  `a = ½ log(X/2π) + iπ/4`, hence the log-linear model
  `‖F(w) − F(u)e^{(w−u)a}‖ ≤ ‖F(u)‖e^{(w−u)α}(e^{|w−u|/8} − 1)` (`norm_xiLine_sub_model_le`);
* beyond `w = 9/2`, `‖F'‖ ≤ (α + 2 + (w + ½)/(2X))‖F‖`;
* on `0 ≤ w ≤ 9/2`, `‖F(w)‖ ≤ 200(6 + X)‖F(9/2)‖`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- `ξ` along the horizontal line through `½ + iX`. -/
def xiLine (X w : ℝ) : ℂ := xi (1 / 2 + w + I * X)

/-- Its derivative in the horizontal direction. -/
def xiLineDeriv (X w : ℝ) : ℂ := deriv xi (1 / 2 + w + I * X)

theorem xiLine_point (X w : ℝ) :
    (1 / 2 + w + I * X : ℂ) = ((w + 1 / 2 : ℝ) : ℂ) + X * I := by
  push_cast; ring

theorem hasDerivAt_xiLine (X w : ℝ) : HasDerivAt (xiLine X) (xiLineDeriv X w) w := by
  have h := (xi_differentiable (1 / 2 + w + I * X)).hasDerivAt
  have hin : HasDerivAt (fun z : ℂ => 1 / 2 + z + I * X) 1 (w : ℂ) :=
    ((hasDerivAt_id (w : ℂ)).const_add (1 / 2)).add_const (I * X)
  have h2 := h.comp (w : ℂ) hin
  rw [mul_one] at h2
  exact h2.comp_ofReal

theorem continuous_xiLineDeriv (X : ℝ) : Continuous (xiLineDeriv X) := by
  have h := (xi_differentiable.contDiff (n := 1)).continuous_deriv le_rfl
  unfold xiLineDeriv
  fun_prop

theorem continuous_xiLine (X : ℝ) : Continuous (xiLine X) :=
  continuous_iff_continuousAt.mpr fun w => (hasDerivAt_xiLine X w).continuousAt

theorem integrable_exp_mul_norm_xiLine {t : ℝ} (ht : 0 < t) (X : ℝ) :
    Integrable (fun w => Real.exp (-(w ^ 2 / (16 * t))) * ‖xiLine X w‖) := by
  have h := (integrable_gaussDensity_mul_xi (t := 4 * t) (by positivity) (X : ℂ)).norm
  refine (h.const_mul ((16 * Real.pi * t) ^ (1 / 2 : ℝ))).congr (Eventually.of_forall fun w => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos (by positivity) _)]
  unfold gaussDensity xiLine
  have hpt : (1 / 2 : ℂ) + I * X + w = 1 / 2 + w + I * X := by ring
  rw [hpt]
  have hc : (4 * Real.pi * (4 * t)) = 16 * Real.pi * t := by ring
  have he : -(w ^ 2 / (4 * (4 * t))) = -(w ^ 2 / (16 * t)) := by ring_nf
  rw [hc, he, ← mul_assoc, ← mul_assoc, ← Real.rpow_add (by positivity)]
  norm_num

theorem xiLineDeriv_eq {X w : ℝ} (hw : 1 / 2 < w) :
    xiLineDeriv X w = logDeriv xi (((w + 1 / 2 : ℝ) : ℂ) + X * I) * xiLine X w := by
  unfold xiLineDeriv xiLine
  rw [xiLine_point, logDeriv_apply]
  have hne : xi (((w + 1 / 2 : ℝ) : ℂ) + X * I) ≠ 0 :=
    xi_ne_zero_of_one_lt_re (by simp; linarith)
  rw [div_mul_cancel₀ _ hne]

/-- **The slope on the window.** -/
theorem norm_xiLineDeriv_sub_le {X w : ℝ} (hX : 200 ≤ X) (hw1 : 9 / 2 ≤ w)
    (hwW : w ≤ X / 32 - 1 / 2) :
    ‖xiLineDeriv X w - horizontalSlope X * xiLine X w‖ ≤ 1 / 8 * ‖xiLine X w‖ := by
  rw [xiLineDeriv_eq (by linarith), ← sub_mul, norm_mul]
  gcongr
  exact norm_logDeriv_xi_sub_horizontalSlope_le (by linarith) (by linarith) hX

/-- **The slope beyond `w = 9/2`.** -/
theorem norm_xiLineDeriv_le {X w : ℝ} (hX : 200 ≤ X) (hw1 : 9 / 2 ≤ w) :
    ‖xiLineDeriv X w‖ ≤
      (Real.log (X / (2 * Real.pi)) / 2 + 2 + (w + 1 / 2) / (2 * X)) * ‖xiLine X w‖ := by
  rw [xiLineDeriv_eq (by linarith), norm_mul]
  gcongr
  exact norm_logDeriv_xi_horizontal_le (by linarith) hX

/-- **The strip comparison.** -/
theorem norm_xiLine_le_strip {X w : ℝ} (hX : 8 ≤ X) (hw0 : 0 ≤ w) (hw : w ≤ 9 / 2) :
    ‖xiLine X w‖ ≤ 200 * (6 + X) * ‖xiLine X (9 / 2)‖ := by
  unfold xiLine
  rw [xiLine_point, xiLine_point]
  have := norm_xi_horizontal_le_mul_norm_xi_five (σ := w + 1 / 2) (by linarith) (by linarith) hX
  norm_num at this ⊢
  exact this

/-- **The log-linear model on the window.** -/
theorem norm_xiLine_sub_model_le {X u w : ℝ} (hX : 200 ≤ X)
    (hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) (hw : w ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) :
    ‖xiLine X w - xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ ≤
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) *
        (Real.exp (1 / 8 * |w - u|) - 1) := by
  have hsub : uIcc u w ⊆ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2) :=
    uIcc_subset_Icc hu hw
  exact GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (by norm_num)
    (fun x _ => hasDerivAt_xiLine X x)
    (fun x hx => norm_xiLineDeriv_sub_le hX (hsub hx).1 (hsub hx).2)

/-- The model bounds `‖F(w)‖` on the window. -/
theorem norm_xiLine_le_model {X u w : ℝ} (hX : 200 ≤ X)
    (hu : u ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) (hw : w ∈ Icc (9 / 2 : ℝ) (X / 32 - 1 / 2)) :
    ‖xiLine X w‖ ≤
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) * Real.exp (1 / 8 * |w - u|) := by
  have h := norm_xiLine_sub_model_le hX hu hw
  have hn : ‖xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ =
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) := by
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  have := norm_sub_norm_le (xiLine X w) (xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X))
  rw [hn] at this
  nlinarith

/-- **Growth beyond the window.** For `9/2 ≤ W ≤ w`,
`‖F(w)‖ ≤ ‖F(W)‖ exp((w − W)(α + 2 + (w + ½)/(2X)))`. -/
theorem norm_xiLine_le_far {X W w : ℝ} (hX : 200 ≤ X) (hW : 9 / 2 ≤ W) (hWw : W ≤ w) :
    ‖xiLine X w‖ ≤ ‖xiLine X W‖ *
      Real.exp ((Real.log (X / (2 * Real.pi)) / 2 + 2 + (w + 1 / 2) / (2 * X)) * (w - W)) := by
  refine GaloisForLFunctions.HTGeometry.norm_le_mul_exp_of_norm_deriv_le_Icc hWw
    (fun x _ => hasDerivAt_xiLine X x) fun x hx => ?_
  refine (norm_xiLineDeriv_le hX (by linarith [hx.1])).trans ?_
  gcongr
  exact hx.2

end

end RHTower.DeBruijn
