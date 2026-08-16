import Mathlib

/-!
# A bounded function with a bounded second derivative has a bounded first derivative

The Landau-type inequality in the form needed for an oscillator: on a unit interval,

```text
|w'(u)|  ≤  |w(u+1)| + |w(u)| + (1/2)·sup |w''| .
```

The proof is one integration by parts in disguise: `g(t) = w(t) + (u+1−t)w'(t)` has derivative
`(u+1−t)w''(t)`, so `w(u+1) − w(u) − w'(u) = ∫_u^{u+1}(u+1−t)w''(t)dt`, and the kernel integrates to
`1/2`.

This is what converts an envelope bound on a solution of `w'' + (1+q)w = 0` into an envelope bound on
its energy: the second derivative is `−(1+q)w`, already controlled by the envelope, so the first
derivative is too.  No asymptotic expansion and no evaluation of the solution is involved.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **Landau on a unit interval.** -/
theorem abs_deriv_le_of_bounded {w Dw DDw : ℝ → ℝ} {u C M : ℝ}
    (hw : ∀ t ∈ Icc u (u + 1), HasDerivAt w (Dw t) t)
    (hDw : ∀ t ∈ Icc u (u + 1), HasDerivAt Dw (DDw t) t)
    (hDDc : ContinuousOn DDw (Icc u (u + 1)))
    (hC : ∀ t ∈ Icc u (u + 1), |w t| ≤ C)
    (hM : ∀ t ∈ Icc u (u + 1), |DDw t| ≤ M) :
    |Dw u| ≤ 2 * C + M / 2 := by
  have hu1 : u ≤ u + 1 := by linarith
  have huIcc : uIcc u (u + 1) = Icc u (u + 1) := uIcc_of_le hu1
  set g : ℝ → ℝ := fun t => w t + (u + 1 - t) * Dw t with hgdef
  have hg : ∀ t ∈ uIcc u (u + 1), HasDerivAt g ((u + 1 - t) * DDw t) t := by
    intro t ht
    rw [huIcc] at ht
    have h1 := hw t ht
    have h2 : HasDerivAt (fun z : ℝ => u + 1 - z) (-1) t := (hasDerivAt_id t).const_sub (u + 1)
    have h3 := h2.mul (hDw t ht)
    have h := h1.add h3
    refine h.congr_deriv ?_
    ring
  have hker : ContinuousOn (fun t : ℝ => (u + 1 - t) * DDw t) (uIcc u (u + 1)) := by
    rw [huIcc]
    exact (by fun_prop : ContinuousOn (fun t : ℝ => u + 1 - t) (Icc u (u + 1))).mul hDDc
  have hint : IntervalIntegrable (fun t : ℝ => (u + 1 - t) * DDw t)
      MeasureTheory.volume u (u + 1) := hker.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint
  have hgu : g u = w u + Dw u := by
    rw [hgdef]
    simp
  have hgu1 : g (u + 1) = w (u + 1) := by
    rw [hgdef]
    simp
  rw [hgu, hgu1] at hFTC
  -- the kernel integral
  have habs : |∫ t in u..(u + 1), (u + 1 - t) * DDw t| ≤ M / 2 := by
    have hmono : (∫ t in u..(u + 1), |(u + 1 - t) * DDw t|)
        ≤ ∫ t in u..(u + 1), M * (u + 1 - t) := by
      refine intervalIntegral.integral_mono_on hu1 hint.abs ?_ fun t ht => ?_
      · exact ((continuousOn_const.mul (by fun_prop))).intervalIntegrable_of_Icc hu1
      · have h1 : |u + 1 - t| = u + 1 - t := abs_of_nonneg (by linarith [ht.2])
        rw [abs_mul, h1]
        have hMt := hM t ht
        nlinarith [hMt, abs_nonneg (DDw t), (by linarith [ht.2] : (0:ℝ) ≤ u + 1 - t)]
    have hval : (∫ t in u..(u + 1), M * (u + 1 - t)) = M / 2 := by
      have hprim : ∀ t ∈ uIcc u (u + 1),
          HasDerivAt (fun z : ℝ => M * (-(u + 1 - z) ^ 2 / 2)) (M * (u + 1 - t)) t := by
        intro t _
        have h2 : HasDerivAt (fun z : ℝ => u + 1 - z) (-1) t := (hasDerivAt_id t).const_sub (u + 1)
        have h3 : HasDerivAt (fun z : ℝ => -(u + 1 - z) ^ 2 / 2) (u + 1 - t) t := by
          have := (h2.pow 2).neg.div_const 2
          refine this.congr_deriv ?_
          ring
        exact h3.const_mul M
      have hint2 : IntervalIntegrable (fun t : ℝ => M * (u + 1 - t)) MeasureTheory.volume u (u + 1) :=
        (by fun_prop : Continuous fun t : ℝ => M * (u + 1 - t)).intervalIntegrable _ _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hint2]
      simp
      ring
    have habs' := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume)
      (f := fun t : ℝ => (u + 1 - t) * DDw t) hu1
    linarith [habs', hmono, hval.le, hval.ge]
  have h1 := hC u (left_mem_Icc.2 hu1)
  have h2 := hC (u + 1) (right_mem_Icc.2 hu1)
  have hDwval : Dw u = w (u + 1) - w u - ∫ t in u..(u + 1), (u + 1 - t) * DDw t := by
    linarith [hFTC]
  rw [hDwval]
  calc |w (u + 1) - w u - ∫ t in u..(u + 1), (u + 1 - t) * DDw t|
      ≤ |w (u + 1) - w u| + |∫ t in u..(u + 1), (u + 1 - t) * DDw t| := abs_sub _ _
    _ ≤ (|w (u + 1)| + |w u|) + M / 2 := by
        have := abs_sub (w (u + 1)) (w u)
        linarith [habs, this]
    _ ≤ 2 * C + M / 2 := by linarith

end GaloisForLFunctions.HTGeometry

end
