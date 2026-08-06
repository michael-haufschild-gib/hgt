import GaloisForLFunctions.HTGeometry.BarnesConeKernelShift
import GaloisForLFunctions.HTGeometry.BarnesDoubleZetaDeepContinuation

/-!
# The shift identity descends to the Taylor data

The kernel shift `F_2(x,t) = F_2(x+omega_1,t) + F_1(omega_2;x,t)` becomes, for the extended kernels,
`A_2(x,z) = A_2(x+omega_1,z) + z A_1(omega_2;x,z)` -- valid near the origin, where the two geometric
denominators do not vanish.

Peeling one factor shifts the iterated divided difference by the peeled function, so the Taylor
coefficients satisfy `a_1(x) = a_1(x+omega_1) + 1/omega_2` and
`a_2(x) = a_2(x+omega_1) + b_1(omega_2;x)`, and the cubic remainder inherits the identity exactly.
These are the ingredients that make the shift equation of the continued zeta an algebraic
consequence rather than an analytic continuation argument.
-/

open Complex Filter Metric
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The divided difference only depends on the germ. -/
theorem analyticSlope_congr {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝 c] g) :
    analyticSlope f c =ᶠ[𝓝 c] analyticSlope g c := by
  have hc : f c = g c := h.eq_of_nhds
  have hderiv : deriv f c = deriv g c := h.deriv_eq
  filter_upwards [h] with z hz
  rcases eq_or_ne z c with rfl | hzc
  · rw [analyticSlope_self, analyticSlope_self, hderiv]
  · rw [analyticSlope_of_ne hzc, analyticSlope_of_ne hzc, hz, hc]

theorem analyticSlopeIter_congr {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝 c] g) (n : ℕ) :
    analyticSlopeIter f c n =ᶠ[𝓝 c] analyticSlopeIter g c n := by
  induction n generalizing f g with
  | zero => exact h
  | succ n ih =>
      rw [analyticSlopeIter_succ', analyticSlopeIter_succ']
      exact ih (analyticSlope_congr h)

theorem analyticSlopeIter_eq_of_eventuallyEq {f g : ℂ → ℂ} {c : ℂ} (h : f =ᶠ[𝓝 c] g) (n : ℕ) :
    analyticSlopeIter f c n c = analyticSlopeIter g c n c :=
  (analyticSlopeIter_congr h n).eq_of_nhds

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The extended cone kernel's shift identity, near the origin.**  Away from the lattice of poles
of the two geometric factors, shifting by a period peels off the ray kernel. -/
theorem barnesConeKernelAnalytic_shift_eventually {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0)
    (x : ℂ) :
    barnesConeKernelAnalytic o1 o2 x
      =ᶠ[𝓝 (0 : ℂ)] fun z => barnesConeKernelAnalytic o1 o2 (x + o1) z
        + (z - 0) * barnesRayKernelAnalytic o2 x z := by
  have hn1 : 0 < ‖o1‖ := norm_pos_iff.mpr h1
  have hn2 : 0 < ‖o2‖ := norm_pos_iff.mpr h2
  set r : ℝ := min (2 * Real.pi / ‖o1‖) (2 * Real.pi / ‖o2‖) with hrdef
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  · have hzn : ‖z‖ < r := by
      simpa [Complex.dist_eq, sub_zero] using Metric.mem_ball.mp hz
    have hb1 : ‖o1 * z‖ < 2 * Real.pi := by
      rw [norm_mul]
      have : ‖z‖ < 2 * Real.pi / ‖o1‖ := lt_of_lt_of_le hzn (min_le_left _ _)
      calc ‖o1‖ * ‖z‖ < ‖o1‖ * (2 * Real.pi / ‖o1‖) := by exact mul_lt_mul_of_pos_left this hn1
        _ = 2 * Real.pi := by field_simp
    have hb2 : ‖o2 * z‖ < 2 * Real.pi := by
      rw [norm_mul]
      have : ‖z‖ < 2 * Real.pi / ‖o2‖ := lt_of_lt_of_le hzn (min_le_right _ _)
      calc ‖o2‖ * ‖z‖ < ‖o2‖ * (2 * Real.pi / ‖o2‖) := by exact mul_lt_mul_of_pos_left this hn2
        _ = 2 * Real.pi := by field_simp
    have hd1 : (1 : ℂ) - Complex.exp (-(o1 * z)) ≠ 0 :=
      one_sub_exp_neg_mul_ne_zero h1 hz0 hb1
    have hd2 : (1 : ℂ) - Complex.exp (-(o2 * z)) ≠ 0 :=
      one_sub_exp_neg_mul_ne_zero h2 hz0 hb2
    have hexp : Complex.exp (-((x + o1) * z))
        = Complex.exp (-(x * z)) * Complex.exp (-(o1 * z)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have key : ∀ E a b w : ℂ, (1 : ℂ) - a ≠ 0 → (1 : ℂ) - b ≠ 0 →
        E * (w / (1 - a)) * (w / (1 - b))
          = E * a * (w / (1 - a)) * (w / (1 - b)) + w * (E * (w / (1 - b))) := by
      intro E a b w ha hb
      field_simp
      ring
    rw [sub_zero, barnesConeKernelAnalytic, barnesConeKernelAnalytic, barnesRayKernelAnalytic]
    simp only [cylKernelFactor_of_ne hz0]
    rw [hexp]
    exact key _ _ _ _ hd1 hd2

theorem barnesConeLinearCoeff_shift {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0) (x : ℂ) :
    barnesConeLinearCoeff o1 o2 x = barnesConeLinearCoeff o1 o2 (x + o1) + o2⁻¹ := by
  have hB : AnalyticAt ℂ (barnesConeKernelAnalytic o1 o2 (x + o1)) 0 :=
    analyticAt_barnesConeKernelAnalytic h1 h2 (x + o1)
  have hC : AnalyticAt ℂ (barnesRayKernelAnalytic o2 x) 0 :=
    analyticAt_barnesRayKernelAnalytic h2 x
  have hcongr := analyticSlopeIter_eq_of_eventuallyEq
    (barnesConeKernelAnalytic_shift_eventually h1 h2 x) 1
  rw [analyticSlopeIter_add_sub_mul hB hC 0] at hcongr
  simp only [analyticSlopeIter_succ, analyticSlopeIter_zero, analyticSlope_self] at hcongr
  rw [barnesConeLinearCoeff, barnesConeLinearCoeff, hcongr, barnesRayKernelAnalytic_zero]

theorem barnesConeQuadCoeff_shift {o1 o2 : ℂ} (h1 : o1 ≠ 0) (h2 : o2 ≠ 0) (x : ℂ) :
    barnesConeQuadCoeff o1 o2 x
      = barnesConeQuadCoeff o1 o2 (x + o1) + barnesRayLinearCoeff o2 x := by
  have hB : AnalyticAt ℂ (barnesConeKernelAnalytic o1 o2 (x + o1)) 0 :=
    analyticAt_barnesConeKernelAnalytic h1 h2 (x + o1)
  have hC : AnalyticAt ℂ (barnesRayKernelAnalytic o2 x) 0 :=
    analyticAt_barnesRayKernelAnalytic h2 x
  have hcongr := analyticSlopeIter_eq_of_eventuallyEq
    (barnesConeKernelAnalytic_shift_eventually h1 h2 x) 2
  rw [analyticSlopeIter_add_sub_mul hB hC 1] at hcongr
  rw [barnesConeQuadCoeff, barnesConeQuadCoeff, hcongr, barnesRayLinearCoeff]
  simp only [analyticSlopeIter_succ, analyticSlopeIter_zero, analyticSlope_self]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The shift identity of the extended cone kernel on the positive reals.** -/
theorem barnesConeKernelAnalytic_shift_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ)
    {t : ℝ} (ht : 0 < t) :
    barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
      = barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) ((x + o1 : ℝ) : ℂ) (t : ℂ)
        + (t : ℂ) * barnesRayKernelAnalytic (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  rw [barnesConeKernelAnalytic_ofReal o1 o2 x (ne_of_gt ht),
    barnesConeKernelAnalytic_ofReal o1 o2 (x + o1) (ne_of_gt ht),
    barnesRayKernelAnalytic_ofReal o2 x (ne_of_gt ht),
    barnesConeKernel_shift h1 h2 x ht]
  ring

/-- **The cubic remainder inherits the shift identity.** -/
theorem barnesConeCubicRemainder_shift {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ)
    {t : ℝ} (ht : 0 < t) :
    barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
      = barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) ((x + o1 : ℝ) : ℂ) (t : ℂ)
        + barnesRayRemainder (o2 : ℂ) (x : ℂ) (t : ℂ) := by
  have ho1 : (o1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1)
  have ho2 : (o2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h2)
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hcast : ((x + o1 : ℝ) : ℂ) = (x : ℂ) + (o1 : ℂ) := by push_cast; ring
  have hlin := barnesConeLinearCoeff_shift ho1 ho2 (x : ℂ)
  have hquad := barnesConeQuadCoeff_shift ho1 ho2 (x : ℂ)
  rw [← hcast] at hlin hquad
  have hker := barnesConeKernelAnalytic_shift_ofReal h1 h2 x ht
  rw [barnesConeCubicRemainder_of_ne htC, barnesConeCubicRemainder_of_ne htC,
    barnesRayRemainder_of_ne htC, hker, hlin, hquad]
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
