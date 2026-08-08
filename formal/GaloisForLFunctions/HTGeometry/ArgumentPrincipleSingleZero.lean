/-
# The logarithmic-derivative residue at a single zero

If `f = (z − c)^d · g` on a disc with `g` analytic and nowhere zero there, then

  `∮_{|z−c|=r} f′/f = 2πi·d`.

This is the computational core of the argument principle, which mathlib does not have: the
logarithmic derivative splits as `d/(z − c) + g′/g`, the first term integrates to `2πi·d` and the
second to `0` because `g′/g` is analytic on the disc.

Main result: `circleIntegral_logDeriv_of_factor`.
-/
import Mathlib.Analysis.Complex.CauchyIntegral

namespace GaloisForLFunctions.HTGeometry

open Complex Metric intervalIntegral

/-- **The logarithmic-derivative residue at a zero of order `d`.** -/
theorem circleIntegral_logDeriv_of_factor {f g : ℂ → ℂ} {c : ℂ} {R : ℝ} (d : ℕ)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgne : ∀ z ∈ ball c R, g z ≠ 0)
    (hf : ∀ z ∈ ball c R, f z = (z - c) ^ d * g z)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    (∮ z in C(c, r), deriv f z / f z) = 2 * Real.pi * Complex.I * (d : ℂ) := by
  have hRpos : 0 < R := lt_trans hr hrR
  have hsub : closedBall c r ⊆ ball c R := closedBall_subset_ball hrR
  -- `g` is differentiable at every point of the closed disc of radius `r`
  have hgd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ g z := fun z hz =>
    hg.differentiableAt (isOpen_ball.mem_nhds (hsub hz))
  -- the analytic logarithmic derivative of `g`
  have hLg : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c r) := by
    intro z hz
    have hzR : z ∈ ball c R := hsub (ball_subset_closedBall hz)
    have hga : AnalyticAt ℂ g z := hg.analyticAt (isOpen_ball.mem_nhds hzR)
    exact (((hga.deriv).div hga (hgne z hzR)).differentiableAt).differentiableWithinAt
  have hLgc : ContinuousOn (fun z => deriv g z / g z) (closedBall c r) := by
    intro z hz
    have hzR : z ∈ ball c R := hsub hz
    have hga : AnalyticAt ℂ g z := hg.analyticAt (isOpen_ball.mem_nhds hzR)
    exact (((hga.deriv).div hga (hgne z hzR)).continuousAt).continuousWithinAt
  -- the splitting of the logarithmic derivative on the circle
  have hsplit : ∀ z ∈ sphere c r,
      deriv f z / f z = (d : ℂ) * (z - c)⁻¹ + deriv g z / g z := by
    intro z hz
    have hzr : dist z c = r := mem_sphere.mp hz
    have hzR : z ∈ ball c R := hsub (by rw [mem_closedBall, hzr])
    have hzc : z - c ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, dist_self] at hzr
      exact hr.ne hzr
    have hgz : g z ≠ 0 := hgne z hzR
    have hev : f =ᶠ[nhds z] fun w => (w - c) ^ d * g w := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw using hf w hw
    have hgda : DifferentiableAt ℂ g z := hg.differentiableAt (isOpen_ball.mem_nhds hzR)
    have hderiv : deriv f z = (d : ℂ) * (z - c) ^ (d - 1) * g z + (z - c) ^ d * deriv g z := by
      rw [hev.deriv_eq]
      rw [deriv_fun_mul (by fun_prop) hgda]
      congr 1
      rw [deriv_fun_pow (by fun_prop)]
      simp
    have hfz : f z = (z - c) ^ d * g z := hf z hzR
    rw [hderiv, hfz]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hpow : (z - c) ^ d = (z - c) ^ (d - 1) * (z - c) := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hpow]
      field_simp
  -- integrate the two pieces
  have hint1 : (∮ z in C(c, r), (d : ℂ) * (z - c)⁻¹) = 2 * Real.pi * Complex.I * (d : ℂ) := by
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]
    ring
  have hint2 : (∮ z in C(c, r), deriv g z / g z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
      hLgc (fun z hz => (hLg z hz.1).differentiableAt (isOpen_ball.mem_nhds hz.1))
  have hci1 : CircleIntegrable (fun z : ℂ => (d : ℂ) * (z - c)⁻¹) c r := by
    refine ContinuousOn.circleIntegrable hr.le ?_
    intro z hz
    have hzr : dist z c = r := mem_sphere.mp hz
    have hzc : z - c ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      rw [h, dist_self] at hzr
      exact hr.ne hzr
    exact (continuousAt_const.mul
      ((continuousAt_id.sub continuousAt_const).inv₀ hzc)).continuousWithinAt
  have hci2 : CircleIntegrable (fun z : ℂ => deriv g z / g z) c r :=
    (hLgc.mono (fun z hz => by
      simpa [mem_closedBall, dist_eq_norm] using (sphere_subset_closedBall hz))).circleIntegrable hr.le
  calc (∮ z in C(c, r), deriv f z / f z)
      = ∮ z in C(c, r), ((d : ℂ) * (z - c)⁻¹ + deriv g z / g z) :=
        circleIntegral.integral_congr hr.le hsplit
    _ = (∮ z in C(c, r), (d : ℂ) * (z - c)⁻¹) + ∮ z in C(c, r), deriv g z / g z :=
        circleIntegral.integral_add hci1 hci2
    _ = 2 * Real.pi * Complex.I * (d : ℂ) := by rw [hint1, hint2, add_zero]

end GaloisForLFunctions.HTGeometry
