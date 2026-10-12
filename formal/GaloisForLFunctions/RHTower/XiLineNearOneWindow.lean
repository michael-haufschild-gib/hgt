import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne
import GaloisForLFunctions.RHTower.XiLineHalfGaussInstance

/-!
# The log-linear model of `ξ` on a window starting just right of `σ = 1`

Put `F(w) = ξ(½ + w + iX)` (`xiLine X w`) and `a = ½ log(X/2π) + iπ/4`. For `ε > 0` let the window
be `½ + ε ≤ w ≤ X/32 − ½`, so that `1 + ε ≤ Re s ≤ X/32`. With `η = 1/ε + 3`:

* `‖F'(w) − aF(w)‖ ≤ η‖F(w)‖` on the window (`norm_xiLineDeriv_sub_le_near`), from the slope model
  `norm_logDeriv_xi_sub_horizontalSlope_le_near`;
* `‖F(w) − F(u)e^{(w−u)a}‖ ≤ ‖F(u)‖e^{(w−u)α}(e^{η|w−u|} − 1)` for `u, w` in the window
  (`norm_xiLine_sub_model_le_near`), by the log-linear Grönwall lemma.

These are the window hypotheses of `norm_halfGaussTransform_sub_main_le` and
`norm_slope_sub_mul_le` with window start `½ + ε` in place of `9/2`.
-/

open Complex Set

namespace RHTower.DeBruijn

noncomputable section

/-- **The slope on the near window.** -/
theorem norm_xiLineDeriv_sub_le_near {X w ε : ℝ} (hX : 200 ≤ X) (hε : 0 < ε)
    (hw1 : 1 / 2 + ε ≤ w) (hwW : w ≤ X / 32 - 1 / 2) :
    ‖xiLineDeriv X w - horizontalSlope X * xiLine X w‖ ≤ (1 / ε + 3) * ‖xiLine X w‖ := by
  rw [xiLineDeriv_eq (by linarith), ← sub_mul, norm_mul]
  gcongr
  refine (norm_logDeriv_xi_sub_horizontalSlope_le_near (by linarith) (by linarith) hX).trans ?_
  have h1 : 1 / (w + 1 / 2 - 1) ≤ 1 / ε :=
    one_div_le_one_div_of_le hε (by linarith)
  linarith

/-- **The log-linear model on the near window.** -/
theorem norm_xiLine_sub_model_le_near {X u w ε : ℝ} (hX : 200 ≤ X) (hε : 0 < ε)
    (hu : u ∈ Icc (1 / 2 + ε) (X / 32 - 1 / 2)) (hw : w ∈ Icc (1 / 2 + ε) (X / 32 - 1 / 2)) :
    ‖xiLine X w - xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * horizontalSlope X)‖ ≤
      ‖xiLine X u‖ * Real.exp ((w - u) * (horizontalSlope X).re) *
        (Real.exp ((1 / ε + 3) * |w - u|) - 1) := by
  have hsub : uIcc u w ⊆ Icc (1 / 2 + ε) (X / 32 - 1 / 2) := uIcc_subset_Icc hu hw
  exact GaloisForLFunctions.HTGeometry.norm_sub_mul_exp_le (by positivity)
    (fun x _ => hasDerivAt_xiLine X x)
    (fun x hx => norm_xiLineDeriv_sub_le_near hX hε (hsub hx).1 (hsub hx).2)

end

end RHTower.DeBruijn
