import Mathlib

/-!
# The Mellin step for an antiderivative

For a locally integrable `r` on `[1,∞)` and `Re μ > 0`,

```text
μ ∫_1^∞ ( ∫_1^x r(t) dt ) x^{-μ-1} dx  =  ∫_1^∞ r(t) t^{-μ} dt ,
```

which is the step that trades one factor of `x^{-1}` for an antiderivative in Andersson's iterated
Mellin representation.  The proof is Fubini on `{(x,t) : 1 < t ≤ x}`, not integration by parts, so
no differentiability of the antiderivative is needed — which matters because the first antiderivative
in the chain is a step function.
-/

noncomputable section

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

theorem integral_Ioi_cpow_tail {μ : ℂ} (hμ : 0 < μ.re) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioi t, (x : ℂ) ^ (-μ - 1)) = (t : ℂ) ^ (-μ) / μ := by
  have hlt : (-μ - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  rw [integral_Ioi_cpow_of_lt hlt ht]
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h] at hμ
    simp at hμ
  have hexp : -μ - 1 + 1 = -μ := by ring
  rw [hexp]
  field_simp

/-- The kernel whose double integral realizes the Mellin step. -/
def mellinStepKernel (r : ℝ → ℂ) (μ : ℂ) (x t : ℝ) : ℂ :=
  Set.indicator (Set.Iic x) (fun t => r t * (x : ℂ) ^ (-μ - 1)) t

theorem norm_mellinStepKernel (r : ℝ → ℂ) (μ : ℂ) {x t : ℝ} (hx : 0 < x) :
    ‖mellinStepKernel r μ x t‖
      = Set.indicator (Set.Iic x) (fun t => ‖r t‖ * x ^ (-μ.re - 1)) t := by
  classical
  rw [mellinStepKernel]
  by_cases h : t ∈ Set.Iic x
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, norm_mul,
      norm_cpow_eq_rpow_re_of_pos hx]
    simp [Complex.sub_re, Complex.neg_re]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, norm_zero]

theorem integral_mellinStepKernel_snd {r : ℝ → ℂ} {μ : ℂ} {x : ℝ} (hx : 1 ≤ x)
    (hr : IntegrableOn r (Set.Ioc 1 x)) :
    (∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = (∫ t in (1:ℝ)..x, r t) * (x : ℂ) ^ (-μ - 1) := by
  classical
  have hsplit : (∫ t in Set.Ioi (1:ℝ), mellinStepKernel r μ x t)
      = ∫ t in Set.Ioi (1:ℝ) ∩ Set.Iic x, r t * (x : ℂ) ^ (-μ - 1) := by
    simp only [mellinStepKernel]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic]
  rw [hsplit]
  have hset : Set.Ioi (1:ℝ) ∩ Set.Iic x = Set.Ioc 1 x := by
    ext y
    simp [Set.mem_inter_iff, Set.mem_Ioc]
  rw [hset, intervalIntegral.integral_of_le hx, MeasureTheory.integral_mul_const]

end GaloisForLFunctions.HTGeometry

end
