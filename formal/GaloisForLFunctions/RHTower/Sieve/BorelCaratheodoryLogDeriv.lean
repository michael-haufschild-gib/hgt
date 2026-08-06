import GaloisForLFunctions.RHTower.ArgumentVariation
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The logarithmic derivative of a bounded zero-free function

If `g` is analytic and zero-free on a disc and `‖g‖ ≤ M ‖g c‖` there, then an analytic logarithm
`h` with `h c = 0` has real part at most `log M`, so the Borel–Carathéodory bound controls `‖h‖`
itself on the half-disc, and Cauchy's estimate then controls `h' = g'/g` on the quarter-disc:

```text
‖g'(z)/g(z)‖ ≤ 8 log M / R      for ‖z - c‖ ≤ R/4.
```

This is the step that replaces the mean-value estimate in a zero-free region argument.  The mean
value costs a factor `max‖g‖/R`; the logarithmic derivative costs only `log(max‖g‖)/R`, and that is
the whole difference between the exponents `9` and `1`.
-/

namespace RHTower.Sieve

open Metric Complex

/-- **Borel–Carathéodory plus Cauchy for the logarithmic derivative.** -/
theorem norm_deriv_div_le_of_norm_le {g : ℂ → ℂ} {c z : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 1 < M)
    (hg : AnalyticOnNhd ℂ g (ball c R))
    (hg0 : ∀ w ∈ ball c R, g w ≠ 0)
    (hbound : ∀ w ∈ ball c R, ‖g w‖ ≤ M * ‖g c‖)
    (hz : ‖z - c‖ ≤ R / 4) :
    ‖deriv g z / g z‖ ≤ 8 * Real.log M / R := by
  have hcball : c ∈ ball c R := by simpa using hR
  have hgc0 : g c ≠ 0 := hg0 c hcball
  have hgcpos : (0 : ℝ) < ‖g c‖ := norm_pos_iff.mpr hgc0
  have hlogM : 0 < Real.log M := Real.log_pos hM
  obtain ⟨L, hL, hLexp⟩ := RHTower.exists_analyticOnNhd_exp_eq_ball hR hg hg0
  set h : ℂ → ℂ := fun w => L w - L c with hhdef
  have hhan : AnalyticOnNhd ℂ h (ball c R) := fun w hw =>
    (hL w hw).sub analyticAt_const
  have hhc : h c = 0 := by simp [hhdef]
  -- the real part of the logarithm is the logarithm of the ratio of moduli
  have hRe : ∀ w ∈ ball c R, (h w).re ≤ Real.log M := by
    intro w hw
    have hexp : Complex.exp (h w) = g w / g c := by
      simp only [hhdef, Complex.exp_sub, hLexp w hw, hLexp c hcball]
    have hnorm : Real.exp ((h w).re) = ‖g w‖ / ‖g c‖ := by
      have hcong := congrArg norm hexp
      rwa [Complex.norm_exp, norm_div] at hcong
    have hle : Real.exp ((h w).re) ≤ Real.exp (Real.log M) := by
      rw [hnorm, Real.exp_log (by linarith)]
      rw [div_le_iff₀ hgcpos]
      have := hbound w hw
      linarith
    exact Real.exp_le_exp.mp hle
  have hA : (h c).re < Real.log M := by rw [hhc]; simpa using hlogM
  -- Borel–Carathéodory on the half-disc
  have hhalf : ∀ w ∈ closedBall c (R / 2), ‖h w‖ ≤ 2 * Real.log M := by
    intro w hw
    have hwball : w ∈ ball c R := by
      have : ‖w - c‖ ≤ R / 2 := by simpa [dist_eq_norm] using hw
      exact mem_ball_iff_norm.mpr (by linarith)
    have hbc := RHTower.borel_caratheodory hhan.differentiableOn hRe hA hwball
    rw [hhc] at hbc
    simp only [sub_zero, Complex.zero_re, sub_zero] at hbc
    have hρ : ‖w - c‖ ≤ R / 2 := by simpa [dist_eq_norm] using hw
    have hρ0 : (0 : ℝ) ≤ ‖w - c‖ := norm_nonneg _
    have hden : (0 : ℝ) < R - ‖w - c‖ := by linarith
    have hfac : 2 * ‖w - c‖ / (R - ‖w - c‖) ≤ 2 := by
      rw [div_le_iff₀ hden]
      linarith
    calc ‖h w‖ ≤ 2 * ‖w - c‖ / (R - ‖w - c‖) * Real.log M := hbc
      _ ≤ 2 * Real.log M := by nlinarith [hlogM]
  -- Cauchy's estimate on the quarter-disc
  have hsub : closedBall z (R / 4) ⊆ closedBall c (R / 2) := by
    intro w hw
    have h1 : ‖w - z‖ ≤ R / 4 := by simpa [dist_eq_norm] using hw
    have h2 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub w z c
    simp only [mem_closedBall, dist_eq_norm]
    linarith
  have hsubball : closedBall z (R / 4) ⊆ ball c R := fun w hw => by
    have := hsub hw
    have h1 : ‖w - c‖ ≤ R / 2 := by simpa [dist_eq_norm] using this
    exact mem_ball_iff_norm.mpr (by linarith)
  have hdiff : DifferentiableOn ℂ h (closedBall z (R / 4)) :=
    (hhan.mono hsubball).differentiableOn
  have hdcc : DiffContOnCl ℂ h (ball z (R / 4)) := by
    refine ⟨hdiff.mono ball_subset_closedBall, ?_⟩
    exact hdiff.continuousOn.mono closure_ball_subset_closedBall
  have hsphere : ∀ w ∈ sphere z (R / 4), ‖h w‖ ≤ 2 * Real.log M := by
    intro w hw
    exact hhalf w (hsub (sphere_subset_closedBall hw))
  have hderiv : ‖deriv h z‖ ≤ 2 * Real.log M / (R / 4) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) hdcc hsphere
  -- identify the derivative
  have hzball : z ∈ ball c R := mem_ball_iff_norm.mpr (by linarith)
  have hLd : HasDerivAt L (deriv L z) z := (hL z hzball).differentiableAt.hasDerivAt
  have hexpd : HasDerivAt (fun w => Complex.exp (L w)) (Complex.exp (L z) * deriv L z) z :=
    hLd.cexp
  have hEq : (fun w => Complex.exp (L w)) =ᶠ[nhds z] g := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    exact hLexp w hw
  have hgd : HasDerivAt g (Complex.exp (L z) * deriv L z) z := hexpd.congr_of_eventuallyEq hEq.symm
  have hgz : Complex.exp (L z) = g z := hLexp z hzball
  have hderivg : deriv g z = g z * deriv L z := by
    rw [hgd.deriv, hgz]
  have hderivh : deriv h z = deriv L z := by
    simp only [hhdef]
    exact deriv_sub_const _
  have hgz0 : g z ≠ 0 := hg0 z hzball
  have hquot : deriv g z / g z = deriv L z := by
    rw [hderivg, mul_comm, mul_div_assoc, div_self hgz0, mul_one]
  rw [hquot, ← hderivh]
  calc ‖deriv h z‖ ≤ 2 * Real.log M / (R / 4) := hderiv
    _ = 8 * Real.log M / R := by field_simp; ring

end RHTower.Sieve
