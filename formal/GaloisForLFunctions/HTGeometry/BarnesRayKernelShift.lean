import GaloisForLFunctions.HTGeometry.BarnesDoubleGammaShift

/-!
# The shift identity of the Barnes ray kernel

Shifting the argument of the one-dimensional kernel by its period peels off a bare exponential:

```text
F_1(omega; x, t) = F_1(omega; x + omega, t) + e^(-xt).
```

The same peeling argument as for the cone gives the coefficient identity `b_1(x) = b_1(x+omega) + 1`
and the exact remainder identity, with the peeled function now the elementary `(e^(-xt) - 1)/t`.
These are the ingredients of the difference equation of the one-dimensional Barnes gamma, which is
the classical `log Gamma(x + omega) - log Gamma(x) = log x`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The ray kernel's shift identity.**  Shifting by the period peels off a bare exponential. -/
theorem barnesRayKernel_shift {o : ℝ} (ho : 0 < o) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    barnesRayKernel o x t
      = barnesRayKernel o (x + o) t + ((Real.exp (-x * t) : ℝ) : ℂ) := by
  have hd : (1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ) ≠ 0 := by
    intro hcon
    have hz : ‖(1 : ℂ) - ((Real.exp (-o * t) : ℝ) : ℂ)‖ = 0 := by rw [hcon, norm_zero]
    rw [norm_one_sub_exp_neg_mul_ofReal ho ht] at hz
    linarith [one_sub_exp_neg_mul_ofReal_pos ho ht]
  have hexp : ((Real.exp (-(x + o) * t) : ℝ) : ℂ)
      = ((Real.exp (-x * t) : ℝ) : ℂ) * ((Real.exp (-o * t) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  have key : ∀ E a : ℂ, (1 : ℂ) - a ≠ 0 → E / (1 - a) = E * a / (1 - a) + E := by
    intro E a ha
    field_simp
    ring
  rw [barnesRayKernel, barnesRayKernel, hexp]
  exact key _ _ hd

/-- **The extended ray kernel's shift identity, near the origin.** -/
theorem barnesRayKernelAnalytic_shift_eventually {o : ℂ} (ho : o ≠ 0) (x : ℂ) :
    barnesRayKernelAnalytic o x
      =ᶠ[𝓝 (0 : ℂ)] fun z => barnesRayKernelAnalytic o (x + o) z
        + (z - 0) * Complex.exp (-(x * z)) := by
  have hn : 0 < ‖o‖ := norm_pos_iff.mpr ho
  have hr : 0 < 2 * Real.pi / ‖o‖ := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hzn : ‖z‖ < 2 * Real.pi / ‖o‖ := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_ball.mp hz
    have hb : ‖o * z‖ < 2 * Real.pi := by
      rw [norm_mul]
      calc ‖o‖ * ‖z‖ < ‖o‖ * (2 * Real.pi / ‖o‖) := by exact mul_lt_mul_of_pos_left hzn hn
        _ = 2 * Real.pi := by field_simp
    have hd : (1 : ℂ) - Complex.exp (-(o * z)) ≠ 0 := one_sub_exp_neg_mul_ne_zero ho hz0 hb
    have hexp : Complex.exp (-((x + o) * z))
        = Complex.exp (-(x * z)) * Complex.exp (-(o * z)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have key : ∀ E a w : ℂ, (1 : ℂ) - a ≠ 0 →
        E * (w / (1 - a)) = E * a * (w / (1 - a)) + w * E := by
      intro E a w ha
      field_simp
      ring
    rw [sub_zero, barnesRayKernelAnalytic, barnesRayKernelAnalytic]
    simp only [cylKernelFactor_of_ne hz0]
    rw [hexp]
    exact key _ _ _ hd

theorem barnesRayLinearCoeff_shift {o : ℂ} (ho : o ≠ 0) (x : ℂ) :
    barnesRayLinearCoeff o x = barnesRayLinearCoeff o (x + o) + 1 := by
  have hB : AnalyticAt ℂ (barnesRayKernelAnalytic o (x + o)) 0 :=
    analyticAt_barnesRayKernelAnalytic ho (x + o)
  have hC : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(x * z))) 0 :=
    ((analyticAt_const.mul analyticAt_id).neg).cexp'
  have hcongr := analyticSlopeIter_eq_of_eventuallyEq
    (barnesRayKernelAnalytic_shift_eventually ho x) 1
  rw [analyticSlopeIter_add_sub_mul hB hC 0] at hcongr
  simp only [analyticSlopeIter_succ, analyticSlopeIter_zero, analyticSlope_self] at hcongr
  rw [barnesRayLinearCoeff, barnesRayLinearCoeff, hcongr]
  simp

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem barnesRayKernelAnalytic_shift_ofReal {o : ℝ} (ho : 0 < o) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    barnesRayKernelAnalytic (o : ℂ) (x : ℂ) (t : ℂ)
      = barnesRayKernelAnalytic (o : ℂ) ((x + o : ℝ) : ℂ) (t : ℂ)
        + (t : ℂ) * Complex.exp (-((x : ℂ) * (t : ℂ))) := by
  have hcast : Complex.exp (-((x : ℂ) * (t : ℂ))) = ((Real.exp (-x * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [barnesRayKernelAnalytic_ofReal o x (ne_of_gt ht),
    barnesRayKernelAnalytic_ofReal o (x + o) (ne_of_gt ht),
    barnesRayKernel_shift ho x ht, hcast]
  ring

/-- **The ray remainder inherits the shift identity.** -/
theorem barnesRayRemainder_shift {o : ℝ} (ho : 0 < o) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)
      = barnesRayRemainder (o : ℂ) ((x + o : ℝ) : ℂ) (t : ℂ)
        + (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1) / (t : ℂ) := by
  have hoC : (o : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ho)
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hcast : ((x + o : ℝ) : ℂ) = (x : ℂ) + (o : ℂ) := by push_cast; ring
  have hlin := barnesRayLinearCoeff_shift hoC (x : ℂ)
  rw [← hcast] at hlin
  have hker := barnesRayKernelAnalytic_shift_ofReal ho x ht
  rw [barnesRayRemainder_of_ne htC, barnesRayRemainder_of_ne htC, hker, hlin]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
