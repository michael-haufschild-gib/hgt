import GaloisForLFunctions.HTGeometry.ExpMultiplierRapidDecay
import GaloisForLFunctions.HTGeometry.HalfPlaneGapApproximation

/-!
# Entirety of the two-sided Laplace transform of a compactly supported weight

`logSmoothMultiplier k w = ∫ k(x)e^{wx}dx` is an entire function of `w`: the integral only sees a
compact interval, and there the exponential kernel and its derivative are uniformly bounded on every
unit ball of parameters.  The parametric-entirety criterion
`differentiable_integral_kernel` asks for bounds valid at *every* point of the ambient measure
space, so — exactly as in `TruncatedMellinEntire` — the kernel is composed with a clamp before the
criterion is applied.

## Main results

* `differentiable_logSmoothMultiplier`
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- The clamp keeping a parameter inside `[-T, T]`. -/
def expKernelClamp (T x : ℝ) : ℝ := max (-T) (min T x)

theorem expKernelClamp_abs_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |expKernelClamp T x| ≤ T := by
  rw [abs_le, expKernelClamp]
  constructor
  · exact le_max_left _ _
  · refine max_le (by linarith) (min_le_left _ _)

theorem expKernelClamp_eq_self {T x : ℝ} (h1 : -T ≤ x) (h2 : x ≤ T) :
    expKernelClamp T x = x := by
  rw [expKernelClamp, min_eq_right h2, max_eq_right h1]

theorem measurable_expKernelClamp (T : ℝ) : Measurable (expKernelClamp T) := by
  unfold expKernelClamp
  fun_prop

/-- **The multiplier is entire.** -/
theorem differentiable_logSmoothMultiplier {k : ℝ → ℝ} (hk : Continuous k) {R : ℝ}
    (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) :
    Differentiable ℂ (logSmoothMultiplier k) := by
  set T : ℝ := R + 1 with hTdef
  have hT0 : (0 : ℝ) < T := by rw [hTdef]; linarith
  have hRT : R ≤ T := by rw [hTdef]; linarith
  have hφ : Integrable (fun x : ℝ => ((k x : ℝ) : ℂ)) (volume.restrict (Ioc (-T) T)) := by
    refine (Complex.continuous_ofReal.comp hk).integrableOn_Ioc
  have hrep : ∀ w : ℂ, logSmoothMultiplier k w
      = ∫ x : ℝ, ((k x : ℝ) : ℂ) * Complex.exp (w * (expKernelClamp T x : ℝ))
          ∂(volume.restrict (Ioc (-T) T)) := by
    intro w
    rw [logSmoothMultiplier_eq_intervalIntegral hsupp hR.le hRT w,
      intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [expKernelClamp_eq_self (le_of_lt hx.1) hx.2]
  have hdiff : Differentiable ℂ fun w : ℂ =>
      ∫ x : ℝ, ((k x : ℝ) : ℂ) * Complex.exp (w * (expKernelClamp T x : ℝ))
        ∂(volume.restrict (Ioc (-T) T)) := by
    refine differentiable_integral_kernel _ hφ
      (fun x w => Complex.exp (w * (expKernelClamp T x : ℝ)))
      (fun x w => ((expKernelClamp T x : ℝ) : ℂ) * Complex.exp (w * (expKernelClamp T x : ℝ)))
      ?_ ?_ ?_ ?_
    · intro w
      refine Complex.measurable_exp.comp ?_
      exact (measurable_const.mul ((Complex.measurable_ofReal.comp
        (measurable_expKernelClamp T))))
    · intro w
      refine Measurable.mul ?_ ?_
      · exact Complex.measurable_ofReal.comp (measurable_expKernelClamp T)
      · refine Complex.measurable_exp.comp ?_
        exact (measurable_const.mul ((Complex.measurable_ofReal.comp
          (measurable_expKernelClamp T))))
    · intro x w
      have h1 : HasDerivAt (fun v : ℂ => v * ((expKernelClamp T x : ℝ) : ℂ))
          ((expKernelClamp T x : ℝ) : ℂ) w := by
        simpa using (hasDerivAt_id w).mul_const ((expKernelClamp T x : ℝ) : ℂ)
      have h2 := h1.cexp
      rw [mul_comm] at h2
      exact h2
    · intro w₀
      refine ⟨(T + 1) * Real.exp ((‖w₀‖ + 1) * T), fun x w hw => ?_⟩
      have hwn : ‖w‖ ≤ ‖w₀‖ + 1 := by
        have := mem_ball_iff_norm.1 hw
        calc ‖w‖ = ‖w₀ + (w - w₀)‖ := by ring_nf
          _ ≤ ‖w₀‖ + ‖w - w₀‖ := norm_add_le _ _
          _ ≤ ‖w₀‖ + 1 := by linarith
      have hc : |expKernelClamp T x| ≤ T := expKernelClamp_abs_le hT0.le x
      have hre : (w * ((expKernelClamp T x : ℝ) : ℂ)).re = w.re * expKernelClamp T x := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring
      have hexp : ‖Complex.exp (w * ((expKernelClamp T x : ℝ) : ℂ))‖
          = Real.exp (w.re * expKernelClamp T x) := by
        rw [Complex.norm_exp, hre]
      have hwre : |w.re| ≤ ‖w₀‖ + 1 := le_trans (Complex.abs_re_le_norm w) hwn
      have hle : w.re * expKernelClamp T x ≤ (‖w₀‖ + 1) * T := by
        calc w.re * expKernelClamp T x ≤ |w.re * expKernelClamp T x| := le_abs_self _
          _ = |w.re| * |expKernelClamp T x| := abs_mul _ _
          _ ≤ (‖w₀‖ + 1) * T := by
              refine mul_le_mul hwre hc (abs_nonneg _) ?_
              exact le_trans (norm_nonneg w₀) (by linarith)
      have hbnd : Real.exp (w.re * expKernelClamp T x) ≤ Real.exp ((‖w₀‖ + 1) * T) :=
        Real.exp_le_exp.2 hle
      have hpos : (0 : ℝ) < Real.exp ((‖w₀‖ + 1) * T) := Real.exp_pos _
      constructor
      · rw [hexp]
        nlinarith [hbnd, hpos, hT0]
      · rw [norm_mul, hexp, Complex.norm_real, Real.norm_eq_abs]
        have h1 : |expKernelClamp T x| ≤ T := hc
        nlinarith [hbnd, hpos, hT0, abs_nonneg (expKernelClamp T x)]
  have hfun : logSmoothMultiplier k = fun w : ℂ =>
      ∫ x : ℝ, ((k x : ℝ) : ℂ) * Complex.exp (w * (expKernelClamp T x : ℝ))
        ∂(volume.restrict (Ioc (-T) T)) := funext hrep
  rw [hfun]
  exact hdiff

end GaloisForLFunctions.HTGeometry

end
