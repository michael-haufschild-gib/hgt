import GaloisForLFunctions.RHTower.CompactDiscFirstMeanBound
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Complex Set Metric Real
open scoped ENNReal
noncomputable section
namespace RHTower

/-- Boundary absolute-mean envelope for every point of the inner disc. -/
def compactDiscFirstMeanEnvelope {α : Type*} (F : α → ℂ → ℂ)
    (c : ℂ) (r R : ℝ) (x : α) : ℝ≥0∞ :=
  ENNReal.ofReal ((R / (R - r)) * (2 * Real.pi)⁻¹) *
    ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal (‖F x (circleMap c R θ)‖)

private theorem ofReal_integral_norm_le (F : ℝ → ℂ) (μ : Measure ℝ) :
    ENNReal.ofReal (∫ θ, ‖F θ‖ ∂μ) ≤ ∫⁻ θ, ENNReal.ofReal (‖F θ‖) ∂μ := by
  by_cases hi : Integrable (fun θ => ‖F θ‖) μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))).le
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-- Measurability follows from a single joint boundary integrand. -/
theorem measurable_compactDiscFirstMeanEnvelope {α : Type*} [MeasurableSpace α]
    (F : α → ℂ → ℂ) (hF : Measurable (fun q : α × ℂ => F q.1 q.2))
    (c : ℂ) (r R : ℝ) : Measurable (compactDiscFirstMeanEnvelope F c r R) := by
  have hmap : Measurable (fun q : α × ℝ => (q.1, circleMap c R q.2)) :=
    measurable_fst.prodMk ((continuous_circleMap c R).measurable.comp measurable_snd)
  have hg : Measurable (fun q : α × ℝ => ENNReal.ofReal (‖F q.1 (circleMap c R q.2)‖)) :=
    ENNReal.measurable_ofReal.comp (hF.comp hmap).norm
  exact hg.lintegral_prod_right'.const_mul _

/-- The same measurable envelope dominates the complete inner disc pointwise. -/
theorem norm_le_compactDiscFirstMeanEnvelope {α : Type*} (F : α → ℂ → ℂ)
    (hF : ∀ x, Differentiable ℂ (F x)) (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (x : α) {z : ℂ} (hz : z ∈ closedBall c r) :
    ENNReal.ofReal (‖F x z‖) ≤ compactDiscFirstMeanEnvelope F c r R x := by
  have hR : 0 < R := hr.trans_lt hrR
  have hcoef : 0 ≤ (R / (R - r)) * (2 * Real.pi)⁻¹ := by positivity
  have h := norm_le_circleAverage_norm_of_differentiableOn hr hrR (hF x).differentiableOn hz
  simp only [circleAverage, smul_eq_mul] at h
  rw [← mul_assoc, intervalIntegral.integral_of_le Real.two_pi_pos.le] at h
  apply (ENNReal.ofReal_le_ofReal h).trans
  rw [ENNReal.ofReal_mul hcoef]
  exact mul_le_mul_right (ofReal_integral_norm_le (fun θ => F x (circleMap c R θ))
    (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) _

/-- Tonelli converts a boundary first-moment bound to an expectation bound for
the common compact envelope, with no supremum measurability premise. -/
theorem lintegral_compactDiscFirstMeanEnvelope_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (F : α → ℂ → ℂ)
    (hF : Measurable (fun q : α × ℂ => F q.1 q.2)) (c : ℂ) (r R C : ℝ)
    (hbound : ∀ θ : ℝ,
      (∫⁻ x, ENNReal.ofReal (‖F x (circleMap c R θ)‖) ∂μ) ≤ ENNReal.ofReal C) :
    (∫⁻ x, compactDiscFirstMeanEnvelope F c r R x ∂μ) ≤
      ENNReal.ofReal ((R / (R - r)) * (2 * Real.pi)⁻¹) *
        ENNReal.ofReal C * ENNReal.ofReal (2 * Real.pi) := by
  have hmap : Measurable (fun q : α × ℝ => (q.1, circleMap c R q.2)) :=
    measurable_fst.prodMk ((continuous_circleMap c R).measurable.comp measurable_snd)
  have hg : Measurable (fun q : α × ℝ => ENNReal.ofReal (‖F q.1 (circleMap c R q.2)‖)) :=
    ENNReal.measurable_ofReal.comp (hF.comp hmap).norm
  have hinner : Measurable (fun x : α => ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (‖F x (circleMap c R θ)‖)) := hg.lintegral_prod_right'
  unfold compactDiscFirstMeanEnvelope
  rw [lintegral_const_mul _ hinner, lintegral_lintegral_swap hg.aemeasurable]
  calc
    _ ≤ ENNReal.ofReal ((R / (R - r)) * (2 * Real.pi)⁻¹) *
        ∫⁻ _θ in Ioc (0 : ℝ) (2 * Real.pi), ENNReal.ofReal C :=
      mul_le_mul_right (lintegral_mono (fun θ => hbound θ)) _
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_assoc]

end RHTower
