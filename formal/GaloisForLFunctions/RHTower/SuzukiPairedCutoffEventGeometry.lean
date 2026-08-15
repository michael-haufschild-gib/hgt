import GaloisForLFunctions.RHTower.SuzukiLiteralPairedSourceAssembly
import GaloisForLFunctions.HTGeometry.SmoothTransitionDerivBound

/-!
# The canonical cutoff: uniform derivative bound and event geometry

The scale-buffered cutoff is a product of two transitions in the affine arguments

`A^R(L) = e^L(a−x) − o`,   `A^L(L) = e^L(a+x) + o`,

whose derivatives are `A^R + o` and `A^L − o`.  On the support of the transition derivative the
argument lies in `[0,1]`, so for a puncture orientation of modulus one those derivatives are
bounded by two — and hence the cutoff derivative is bounded by four times the transition constant,
uniformly in the coordinate, the aperture and the scale.  That is `(2)`.

The same support restriction locates the event: with `o = 1` a transition on the right factor
forces `e^L(a−x) ∈ [1,2]`, so the block sits at `−log(a−x)` and has width exactly `log 2`.  That is
`(5)`, and it shows the event blocks are `O(1)` wide and centred at `−log|a∓x| + O(1)`.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Derivatives of the buffer arguments -/

theorem hasDerivAt_rightScaleBufferArgument (a x o L : ℝ) :
    HasDerivAt (fun t => suzukiRightScaleBufferArgument a x o t)
      (suzukiRightScaleBufferArgument a x o L + o) L := by
  have hfun : (fun t => suzukiRightScaleBufferArgument a x o t)
      = fun t => Real.exp t * (a - x) - o := by
    funext t
    exact suzukiRightScaleBufferArgument_eq a x o t
  rw [hfun]
  have h := ((Real.hasDerivAt_exp L).mul_const (a - x)).sub_const o
  rw [suzukiRightScaleBufferArgument_eq]
  have hval : Real.exp L * (a - x) - o + o = Real.exp L * (a - x) := by ring
  rw [hval]
  exact h

theorem hasDerivAt_leftScaleBufferArgument (a x o L : ℝ) :
    HasDerivAt (fun t => suzukiLeftScaleBufferArgument a x o t)
      (suzukiLeftScaleBufferArgument a x o L - o) L := by
  have hfun : (fun t => suzukiLeftScaleBufferArgument a x o t)
      = fun t => Real.exp t * (a + x) + o := by
    funext t
    exact suzukiLeftScaleBufferArgument_eq a x o t
  rw [hfun]
  have h := ((Real.hasDerivAt_exp L).mul_const (a + x)).add_const o
  rw [suzukiLeftScaleBufferArgument_eq]
  have hval : Real.exp L * (a + x) + o - o = Real.exp L * (a + x) := by ring
  rw [hval]
  exact h

/-! ## `(2)`: the uniform derivative bound -/

/-- On the support of the transition derivative the buffer argument lies in `[0,1]`, so the chain
rule factor is at most two. -/
theorem abs_deriv_transition_bufferArgument_le {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    {a x o L : ℝ} (ho : |o| ≤ 1) :
    |deriv Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
        * (suzukiRightScaleBufferArgument a x o L + o)| ≤ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  by_cases hmem : suzukiRightScaleBufferArgument a x o L ∈ Icc (0 : ℝ) 1
  · have hbound : |suzukiRightScaleBufferArgument a x o L + o| ≤ 2 := by
      have h1 := hmem.1
      have h2 := hmem.2
      have ho' := abs_le.mp ho
      rw [abs_le]
      constructor <;> linarith [ho'.1, ho'.2]
    rw [abs_mul]
    calc |deriv Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)|
          * |suzukiRightScaleBufferArgument a x o L + o|
        ≤ Λ * 2 := mul_le_mul (hΛ _) hbound (abs_nonneg _) hΛ0
      _ = 2 * Λ := by ring
  · rw [deriv_smoothTransition_eq_zero_of_notMem hmem, zero_mul, abs_zero]
    linarith

/-- The mirror bound for the left buffer argument. -/
theorem abs_deriv_transition_leftBufferArgument_le {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    {a x o L : ℝ} (ho : |o| ≤ 1) :
    |deriv Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)
        * (suzukiLeftScaleBufferArgument a x o L - o)| ≤ 2 * Λ := by
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  by_cases hmem : suzukiLeftScaleBufferArgument a x o L ∈ Icc (0 : ℝ) 1
  · have hbound : |suzukiLeftScaleBufferArgument a x o L - o| ≤ 2 := by
      have h1 := hmem.1
      have h2 := hmem.2
      have ho' := abs_le.mp ho
      rw [abs_le]
      constructor <;> linarith [ho'.1, ho'.2]
    rw [abs_mul]
    calc |deriv Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)|
          * |suzukiLeftScaleBufferArgument a x o L - o|
        ≤ Λ * 2 := mul_le_mul (hΛ _) hbound (abs_nonneg _) hΛ0
      _ = 2 * Λ := by ring
  · rw [deriv_smoothTransition_eq_zero_of_notMem hmem, zero_mul, abs_zero]
    linarith

/-- **`(2)`: the canonical cutoff has a uniform derivative bound.**  Four times the transition
constant, independent of the aperture, the coordinate, the orientation and the scale. -/
theorem abs_deriv_scaleBufferedCutoff_le {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ)
    (a x o L : ℝ) (ho : |o| ≤ 1) :
    |deriv (fun t => suzukiScaleBufferedCutoff a x o t) L| ≤ 4 * Λ := by
  have hR := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    |>.differentiableAt (x := suzukiRightScaleBufferArgument a x o L) |>.hasDerivAt
  have hL := (Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
    |>.differentiableAt (x := suzukiLeftScaleBufferArgument a x o L) |>.hasDerivAt
  have hcompR : HasDerivAt (fun t => Real.smoothTransition (suzukiRightScaleBufferArgument a x o t))
      (deriv Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
        * (suzukiRightScaleBufferArgument a x o L + o)) L :=
    hR.comp L (hasDerivAt_rightScaleBufferArgument a x o L)
  have hcompL : HasDerivAt (fun t => Real.smoothTransition (suzukiLeftScaleBufferArgument a x o t))
      (deriv Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)
        * (suzukiLeftScaleBufferArgument a x o L - o)) L :=
    hL.comp L (hasDerivAt_leftScaleBufferArgument a x o L)
  have hprod : HasDerivAt (fun t => Real.smoothTransition (suzukiRightScaleBufferArgument a x o t)
        * Real.smoothTransition (suzukiLeftScaleBufferArgument a x o t))
      (deriv Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
          * (suzukiRightScaleBufferArgument a x o L + o)
          * Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)
        + Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
          * (deriv Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)
            * (suzukiLeftScaleBufferArgument a x o L - o))) L := hcompR.mul hcompL
  have hfun : (fun t => suzukiScaleBufferedCutoff a x o t)
      = fun t => Real.smoothTransition (suzukiRightScaleBufferArgument a x o t)
          * Real.smoothTransition (suzukiLeftScaleBufferArgument a x o t) := rfl
  rw [hfun, hprod.deriv]
  have h1 := abs_deriv_transition_bufferArgument_le hΛ (a := a) (x := x) (o := o) (L := L) ho
  have h2 := abs_deriv_transition_leftBufferArgument_le hΛ (a := a) (x := x) (o := o) (L := L) ho
  have hbR : |Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  have hbL : |Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  refine le_trans (abs_add_le _ _) ?_
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans (abs_nonneg _) (hΛ 0)
  have hstep1 : |deriv Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
        * (suzukiRightScaleBufferArgument a x o L + o)
        * Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)| ≤ 2 * Λ := by
    rw [abs_mul]
    calc _ ≤ (2 * Λ) * 1 := mul_le_mul h1 hbL (abs_nonneg _) (by linarith)
      _ = 2 * Λ := by ring
  have hstep2 : |Real.smoothTransition (suzukiRightScaleBufferArgument a x o L)
        * (deriv Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)
          * (suzukiLeftScaleBufferArgument a x o L - o))| ≤ 2 * Λ := by
    rw [abs_mul]
    calc _ ≤ 1 * (2 * Λ) := mul_le_mul hbR h2 (abs_nonneg _) (by norm_num)
      _ = 2 * Λ := by ring
  linarith

/-! ## `(5)`: the event window -/

/-- **`(5)`: the right event block sits at `−log(a−x)` and has width `log 2`.**  A transition on the
right factor forces `e^L(a−x) ∈ [1,2]` for the inward orientation. -/
theorem rightEvent_window {a x L : ℝ} (hax : 0 < a - x)
    (hmem : suzukiRightScaleBufferArgument a x 1 L ∈ Icc (0 : ℝ) 1) :
    -Real.log (a - x) ≤ L ∧ L ≤ Real.log 2 - Real.log (a - x) := by
  rw [suzukiRightScaleBufferArgument_eq] at hmem
  have h1 : (1 : ℝ) ≤ Real.exp L * (a - x) := by linarith [hmem.1]
  have h2 : Real.exp L * (a - x) ≤ 2 := by linarith [hmem.2]
  have hlog1 : Real.log 1 ≤ Real.log (Real.exp L * (a - x)) :=
    Real.log_le_log (by norm_num) h1
  have hlog2 : Real.log (Real.exp L * (a - x)) ≤ Real.log 2 :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_mul (Real.exp_ne_zero L) (ne_of_gt hax), Real.log_exp] at hlog1 hlog2
  rw [Real.log_one] at hlog1
  exact ⟨by linarith, by linarith⟩

end GaloisForLFunctions.RHTower
