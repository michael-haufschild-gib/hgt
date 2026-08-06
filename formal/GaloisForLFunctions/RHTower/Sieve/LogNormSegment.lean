import GaloisForLFunctions.RHTower.ArgumentVariation
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound

/-!
# Transporting `log‖·‖` along a segment

On a disc where an analytic function is zero-free it has an analytic logarithm `L`, and
`‖g z‖ = exp (Re (L z))`, so

```text
log‖g z₁‖ - log‖g z₂‖ = Re (L z₁ - L z₂),
```

which the mean value inequality bounds by `sup‖L'‖ · ‖z₁ - z₂‖ = sup‖g'/g‖ · ‖z₁ - z₂‖.

This is how a bound on the logarithmic derivative transports a lower bound for `‖g‖` from one point
to another — the step that converts `ζ'/ζ = O(log²t)` into a lower bound for `‖ζ‖` off the
abscissa, with no branch-cut bookkeeping.
-/

namespace RHTower.Sieve

open Complex

/-- The mean value inequality along a complex segment. -/
theorem norm_sub_le_segment {L : ℂ → ℂ} {z₁ z₂ : ℂ} {M : ℝ}
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℂ L (z₂ + (t : ℂ) * (z₁ - z₂)))
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv L (z₂ + (t : ℂ) * (z₁ - z₂))‖ ≤ M) :
    ‖L z₁ - L z₂‖ ≤ M * ‖z₁ - z₂‖ := by
  set g : ℝ → ℂ := fun t => L (z₂ + (t : ℂ) * (z₁ - z₂)) with hg
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((z₁ - z₂) * deriv L (z₂ + (t : ℂ) * (z₁ - z₂)))
        (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hinner : HasDerivAt (fun u : ℝ => z₂ + (u : ℂ) * (z₁ - z₂)) (z₁ - z₂) t := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := (h1.mul_const (z₁ - z₂)).const_add z₂
      simpa using h2
    have houter : HasDerivAt L (deriv L (z₂ + (t : ℂ) * (z₁ - z₂)))
        (z₂ + (t : ℂ) * (z₁ - z₂)) := (hdiff t ht).hasDerivAt
    have hcomp := HasDerivAt.scomp t houter hinner
    rw [smul_eq_mul] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(z₁ - z₂) * deriv L (z₂ + (t : ℂ) * (z₁ - z₂))‖ ≤ M * ‖z₁ - z₂‖ := by
    intro t ht
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have hg0 : g 0 = L z₂ := by
    simp only [hg, Complex.ofReal_zero, zero_mul, add_zero]
  have hg1 : g 1 = L z₁ := by
    simp only [hg, Complex.ofReal_one, one_mul]
    congr 1
    ring
  rw [hg0, hg1] at hmvt
  simpa using hmvt

/-- On a zero-free disc, an analytic logarithm has the logarithmic derivative as its derivative. -/
theorem deriv_analyticLog_eq {g L : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg0 : ∀ w ∈ Metric.ball c R, g w ≠ 0)
    (hL : AnalyticOnNhd ℂ L (Metric.ball c R))
    (hLexp : ∀ w ∈ Metric.ball c R, Complex.exp (L w) = g w)
    {z : ℂ} (hz : z ∈ Metric.ball c R) :
    deriv L z = logDeriv g z := by
  have hLd : HasDerivAt L (deriv L z) z := (hL z hz).differentiableAt.hasDerivAt
  have hexpd : HasDerivAt (fun w => Complex.exp (L w)) (Complex.exp (L z) * deriv L z) z :=
    hLd.cexp
  have hEq : (fun w => Complex.exp (L w)) =ᶠ[nhds z] g := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hLexp w hw
  have hgd : HasDerivAt g (Complex.exp (L z) * deriv L z) z :=
    hexpd.congr_of_eventuallyEq hEq.symm
  have hgz : Complex.exp (L z) = g z := hLexp z hz
  have hgz0 : g z ≠ 0 := hg0 z hz
  rw [logDeriv_apply, hgd.deriv, hgz, mul_comm, mul_div_assoc, div_self hgz0, mul_one]

/-- **Transport of `log‖·‖` along a segment.**  On a zero-free disc, the difference of
`log‖g‖` at two points is at most the supremum of `‖g'/g‖` on the segment times the distance. -/
theorem abs_log_norm_sub_le {g : ℂ → ℂ} {c z₁ z₂ : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (Metric.ball c R)) (hg0 : ∀ w ∈ Metric.ball c R, g w ≠ 0)
    (hz₁ : z₁ ∈ Metric.ball c R) (hz₂ : z₂ ∈ Metric.ball c R)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₂ + (t : ℂ) * (z₁ - z₂) ∈ Metric.ball c R)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖logDeriv g (z₂ + (t : ℂ) * (z₁ - z₂))‖ ≤ M) :
    |Real.log ‖g z₁‖ - Real.log ‖g z₂‖| ≤ M * ‖z₁ - z₂‖ := by
  obtain ⟨L, hL, hLexp⟩ := RHTower.exists_analyticOnNhd_exp_eq_ball hR hg hg0
  have hlogval : ∀ w ∈ Metric.ball c R, Real.log ‖g w‖ = (L w).re := by
    intro w hw
    rw [← hLexp w hw, Complex.norm_exp, Real.log_exp]
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℂ L (z₂ + (t : ℂ) * (z₁ - z₂)) := fun t ht =>
    (hL _ (hseg t ht)).differentiableAt
  have hMd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv L (z₂ + (t : ℂ) * (z₁ - z₂))‖ ≤ M := by
    intro t ht
    rw [deriv_analyticLog_eq hg0 hL hLexp (hseg t ht)]
    exact hM t ht
  have hmv := norm_sub_le_segment hdiff hMd
  rw [hlogval z₁ hz₁, hlogval z₂ hz₂]
  have hre : |(L z₁).re - (L z₂).re| = |(L z₁ - L z₂).re| := by
    rw [Complex.sub_re]
  rw [hre]
  exact le_trans (Complex.abs_re_le_norm _) hmv

end RHTower.Sieve
