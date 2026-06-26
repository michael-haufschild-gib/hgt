/-
# The argument principle realized for the modular `λ`

Applies the disk argument principle (`ArgumentPrinciple.circleIntegral_logDeriv_eq_two_pi_I`, itself
built on our own Cauchy theorem `Period.period_point_inside`) to `λ` itself: around any preimage of a
value `w`, the winding number of `λ` is exactly `1`. The zero of `λ − w` is simple (`λ' ≠ 0`,
`ThetaWronskian`), isolated via the divided-difference factoring `analyticAt_simple_factor`.
-/
import GaloisForLFunctions.Bottcher.ArgumentPrinciple
import GaloisForLFunctions.Bottcher.ModularLambdaCovering
open Complex Metric

namespace Bottcher

/-- **Argument principle for `λ`.** Around any preimage `τ₀` of `w` (`λ τ₀ = w`, `Im τ₀ > 0`), for all
small enough radii, `∮ λ'/(λ−w) = 2πi`: `λ` attains `w` exactly once (simple zero, `λ' ≠ 0`). -/
theorem modularLambda_argument_principle {τ₀ : ℂ} (hτ₀ : 0 < τ₀.im) {w : ℂ}
    (hw : modularLambda τ₀ = w) :
    ∃ R > 0, (∮ z in C(τ₀, R), deriv modularLambda z / (modularLambda z - w))
      = 2 * (Real.pi : ℂ) * Complex.I := by
  set H : Set ℂ := {z | 0 < z.im} with hHdef
  have hHopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hman : AnalyticOnNhd ℂ modularLambda H := by
    have hd : DifferentiableOn ℂ modularLambda H :=
      fun z hz => (differentiableAt_modularLambda_of_im_pos hz).differentiableWithinAt
    exact hd.analyticOnNhd hHopen
  set h : ℂ → ℂ := fun z => modularLambda z - w with hh_def
  have hhan : AnalyticOnNhd ℂ h H := hman.sub analyticOnNhd_const
  have hτ₀H : τ₀ ∈ H := hτ₀
  have hderiv_h : ∀ z, deriv h z = deriv modularLambda z := fun z => by
    simp only [hh_def]; exact deriv_sub_const w
  have hz0 : h τ₀ = 0 := by simp [hh_def, hw]
  have hsimple : deriv h τ₀ ≠ 0 := by rw [hderiv_h]; exact modularLambda_deriv_ne_zero' hτ₀
  obtain ⟨u, huan, hfact, huval⟩ := analyticAt_simple_factor (hhan τ₀ hτ₀H) hz0
  have huτ₀ne : u τ₀ ≠ 0 := huval ▸ hsimple
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.eventually_nhds_iff.mp (huan.continuousAt.eventually_ne huτ₀ne)
  set R : ℝ := min (ε₁/2) (τ₀.im/2) with hR_def
  have hRpos : 0 < R := lt_min (by positivity) (by positivity)
  have hRlt_im : R < τ₀.im := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRlt_ε : R < ε₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨R, hRpos, ?_⟩
  have hsub : closedBall τ₀ R ⊆ H := by
    intro z hz
    simp only [hHdef, Set.mem_setOf_eq]
    have hd : ‖z - τ₀‖ ≤ R := by rw [← Complex.dist_eq]; exact hz
    have him : |(z - τ₀).im| ≤ R := le_trans (Complex.abs_im_le_norm (z - τ₀)) hd
    simp only [Complex.sub_im] at him
    have := (abs_le.mp him).1; linarith
  have hne : ∀ z ∈ closedBall τ₀ R, z ≠ τ₀ → h z ≠ 0 := by
    intro z hz hzne
    have hzU : u z ≠ 0 := hball₁ (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hRlt_ε)
    rw [hfact z]
    exact mul_ne_zero (sub_ne_zero.mpr hzne) hzU
  have key := circleIntegral_logDeriv_eq_two_pi_I hRpos.le hHopen hsub (mem_ball_self hRpos)
    hτ₀H hhan hz0 hsimple hne
  rw [← key]
  apply circleIntegral.integral_congr hRpos.le
  intro z _
  show deriv modularLambda z / (modularLambda z - w) = deriv h z / (modularLambda z - w)
  rw [hderiv_h z]

end Bottcher
