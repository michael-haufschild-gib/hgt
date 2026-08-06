import GaloisForLFunctions.HTGeometry.CircleWirtinger
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# The radial derivative of a circle mean

For a `C¹` function `h : ℂ → ℂ` the circle mean `r ↦ ∫_{-π}^{π} h(r e^{iθ}) dθ` is differentiable, and
its derivative is the integral of the radial derivative.  Because the angular derivative integrates
to zero over a closed circle, the holomorphic and antiholomorphic contributions to that integral
agree, so on a circle of nonzero radius the radial derivative of the circle mean is twice the
`∂̄` term alone:

`(d/dr) ∫_{-π}^{π} h(r e^{iθ}) dθ = 2 ∫_{-π}^{π} e^{-iθ} ∂̄h(r e^{iθ}) dθ`.

This is the identity that carries all the information of the Cauchy–Pompeiu formula: integrating it
in `r` and letting the inner radius tend to zero recovers the value at the centre.

* `HTGeometry.hasDerivAt_circleMean` : differentiation under the integral sign.
* `HTGeometry.hasDerivAt_circleMean_dzbar` : only `∂̄` survives.
-/

open Complex Real intervalIntegral MeasureTheory Set

namespace HTGeometry

variable {h : ℂ → ℂ}

section RadialDerivative

/-- The radial derivative of `h` on the circle of radius `s`, as a function of `(s, θ)`. -/
private noncomputable def radialIntegrand (h : ℂ → ℂ) (s θ : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I) * dz h (circleMap 0 s θ)
    + Complex.exp (-(θ * Complex.I)) * dzbar h (circleMap 0 s θ)

private theorem continuous_radialIntegrand_snd (hC : ContDiff ℝ 1 h) (s : ℝ) :
    Continuous fun θ : ℝ => radialIntegrand h s θ := by
  have hc0 : Continuous fun θ : ℝ => circleMap 0 s θ := continuous_circleMap 0 s
  have hcz : Continuous fun θ : ℝ => dz h (circleMap 0 s θ) := (continuous_dz hC).comp hc0
  have hcb : Continuous fun θ : ℝ => dzbar h (circleMap 0 s θ) := (continuous_dzbar hC).comp hc0
  unfold radialIntegrand
  fun_prop

/-- **Differentiation of the circle mean under the integral sign.** -/
theorem hasDerivAt_circleMean (hC : ContDiff ℝ 1 h) (r : ℝ) :
    HasDerivAt (circleMean h)
      (∫ θ in (-π)..π, radialIntegrand h r θ) r := by
  have hd : Differentiable ℝ h := hC.differentiable one_ne_zero
  -- a uniform bound for the radial derivative over a neighbourhood of `r`
  obtain ⟨C, hCbound⟩ :=
    (isCompact_closedBall (0 : ℂ) (|r| + 1)).exists_bound_of_continuousOn
      (f := fun w : ℂ => ‖dz h w‖ + ‖dzbar h w‖)
      (((continuous_dz hC).norm.add (continuous_dzbar hC).norm).continuousOn)
  have hmem : Metric.closedBall r 1 ∈ nhds r := Metric.closedBall_mem_nhds r one_pos
  have hball : ∀ s ∈ Metric.closedBall r 1, ∀ θ : ℝ,
      circleMap 0 s θ ∈ Metric.closedBall (0 : ℂ) (|r| + 1) := by
    intro s hs θ
    have hs' : |s - r| ≤ 1 := by
      simpa [Real.dist_eq] using hs
    have : |s| ≤ |r| + 1 := by
      have := abs_sub_abs_le_abs_sub s r
      linarith
    simpa [Complex.dist_eq, norm_circleMap_zero] using this
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s θ => h (circleMap 0 s θ)) (F' := fun s θ => radialIntegrand h s θ)
    (bound := fun _ => C) (s := Metric.closedBall r 1) hmem ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with s
    exact ((hd.continuous.comp (continuous_circleMap 0 s)).aestronglyMeasurable).restrict
  · exact ((hd.continuous.comp (continuous_circleMap 0 r)).intervalIntegrable _ _)
  · exact ((continuous_radialIntegrand_snd hC r).aestronglyMeasurable).restrict
  · filter_upwards with θ _ s hs
    have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have h2 : ‖Complex.exp (-((θ : ℂ) * Complex.I))‖ = 1 := by
      have hneg : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hneg]
      exact Complex.norm_exp_ofReal_mul_I (-θ)
    calc ‖radialIntegrand h s θ‖
        ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 s θ)‖
          + ‖Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 s θ)‖ :=
          norm_add_le _ _
      _ = ‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖ := by
          rw [norm_mul, norm_mul, h1, h2, one_mul, one_mul]
      _ ≤ C := by
          have := hCbound _ (hball s hs θ)
          calc ‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖
              ≤ ‖‖dz h (circleMap 0 s θ)‖ + ‖dzbar h (circleMap 0 s θ)‖‖ := le_abs_self _
            _ ≤ C := this
  · exact intervalIntegrable_const
  · filter_upwards with θ _ s _
    exact hasDerivAt_circle_radius hd s θ

/-- **On a circle of nonzero radius only `∂̄` contributes to the radial derivative of the circle
mean.** -/
theorem hasDerivAt_circleMean_dzbar (hC : ContDiff ℝ 1 h) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (circleMean h)
      (2 * ∫ θ in (-π)..π,
        Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ)) r := by
  have hkey := circle_angle_integral_eq hC r
  have hcm : ∀ θ : ℝ, circleMap 0 r θ = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    intro θ; simp [circleMap]
  have hconj : ∀ θ : ℝ,
      (starRingEnd ℂ) (circleMap 0 r θ) = (r : ℂ) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
    intro θ
    rw [hcm, map_mul, ← Complex.exp_conj]
    congr 1
    · simp
    · congr 1
      simp
  have hc0 : Continuous fun θ : ℝ => circleMap 0 r θ := continuous_circleMap 0 r
  have hcz : Continuous fun θ : ℝ => dz h (circleMap 0 r θ) := (continuous_dz hC).comp hc0
  have hcb : Continuous fun θ : ℝ => dzbar h (circleMap 0 r θ) := (continuous_dzbar hC).comp hc0
  have hIz : IntervalIntegrable
      (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ))
      MeasureTheory.volume (-π) π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hIb : IntervalIntegrable
      (fun θ : ℝ => Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ))
      MeasureTheory.volume (-π) π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hsplit : (∫ θ in (-π)..π,
      Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ)) =
      ∫ θ in (-π)..π,
        Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ) := by
    have hL : (∫ θ in (-π)..π, circleMap 0 r θ * dz h (circleMap 0 r θ)) =
        (r : ℂ) * ∫ θ in (-π)..π,
          Complex.exp ((θ : ℂ) * Complex.I) * dz h (circleMap 0 r θ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hcm θ]; ring
    have hR : (∫ θ in (-π)..π,
        (starRingEnd ℂ) (circleMap 0 r θ) * dzbar h (circleMap 0 r θ)) =
        (r : ℂ) * ∫ θ in (-π)..π,
          Complex.exp (-((θ : ℂ) * Complex.I)) * dzbar h (circleMap 0 r θ) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      rw [hconj θ]; ring
    rw [hL, hR] at hkey
    exact mul_left_cancel₀ (by exact_mod_cast hr) hkey
  have hmain := hasDerivAt_circleMean hC r
  convert hmain using 1
  unfold radialIntegrand
  rw [intervalIntegral.integral_add hIz hIb, hsplit]
  ring

end RadialDerivative

end HTGeometry
