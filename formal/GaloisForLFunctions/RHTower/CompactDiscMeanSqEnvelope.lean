import GaloisForLFunctions.RHTower.SteinhausEulerSpatialEnvelope

open MeasureTheory Complex Set Metric
open scoped ENNReal
noncomputable section
namespace RHTower

/-- A planar mean-square integral controls every value on the smaller disc. -/
def compactDiscMeanSqEnvelope {α : Type*} (F : α → ℂ → ℂ)
    (c : ℂ) (r ρ : ℝ) (x : α) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.pi * (ρ - r) ^ 2)⁻¹) *
    ∫⁻ z in ball c ρ, ENNReal.ofReal (‖F x z‖ ^ 2)

private theorem ofReal_norm_sq_integral_le (F : ℂ → ℂ) (μ : Measure ℂ) :
    ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂μ) ≤ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2) ∂μ := by
  by_cases hi : Integrable (fun z => ‖F z‖ ^ 2) μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).le
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

/-- The envelope is measurable directly from the joint integrand, with no uncountable
supremum measurability assumption. -/
theorem measurable_compactDiscMeanSqEnvelope {α : Type*} [MeasurableSpace α]
    (F : α → ℂ → ℂ) (hF : Measurable (fun q : α × ℂ => F q.1 q.2))
    (c : ℂ) (r ρ : ℝ) : Measurable (compactDiscMeanSqEnvelope F c r ρ) := by
  have hg : Measurable (fun q : α × ℂ => ENNReal.ofReal (‖F q.1 q.2‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hF.norm.pow_const 2)
  exact (hg.lintegral_prod_right').const_mul _

/-- Entire random functions obey the same pointwise envelope simultaneously on the
whole inner closed disc. -/
theorem norm_sq_le_compactDiscMeanSqEnvelope {α : Type*} (F : α → ℂ → ℂ)
    (hF : ∀ x, Differentiable ℂ (F x)) (c : ℂ) {r ρ : ℝ} (hrρ : r < ρ)
    (x : α) {z : ℂ} (hz : z ∈ closedBall c r) :
    ENNReal.ofReal (‖F x z‖ ^ 2) ≤ compactDiscMeanSqEnvelope F c r ρ x := by
  have ha : 0 < ρ - r := sub_pos.mpr hrρ
  have harea : 0 < Real.pi * (ρ - r) ^ 2 := by positivity
  have hsub : ball z (ρ - r) ⊆ ball c ρ := by
    intro w hw
    have hwz : dist w z < ρ - r := hw
    have hzc : dist z c ≤ r := hz
    have htri := dist_triangle w z c
    change dist w c < ρ
    linarith
  have hmean := norm_sq_value_mul_area_le_integral_ball_local (F x) z ha
    (hF x).differentiableOn (hF x).continuous.continuousOn
  have hm := mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr harea.le)
  have heq : (Real.pi * (ρ - r) ^ 2)⁻¹ *
      (Real.pi * (ρ - r) ^ 2 * ‖F x z‖ ^ 2) = ‖F x z‖ ^ 2 := by
    field_simp [harea.ne']
  rw [heq] at hm
  apply (ENNReal.ofReal_le_ofReal hm).trans
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr harea.le)]
  exact mul_le_mul_right ((ofReal_norm_sq_integral_le _ _).trans
    (lintegral_mono_set hsub)) _

/-- Tonelli transfers any actual pointwise second-moment bound on the outer disc
into the expectation of the common compact envelope. -/
theorem lintegral_compactDiscMeanSqEnvelope_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (F : α → ℂ → ℂ)
    (hF : Measurable (fun q : α × ℂ => F q.1 q.2)) (c : ℂ) (r ρ C : ℝ)
    (hbound : ∀ z ∈ ball c ρ,
      (∫⁻ x, ENNReal.ofReal (‖F x z‖ ^ 2) ∂μ) ≤ ENNReal.ofReal C) :
    (∫⁻ x, compactDiscMeanSqEnvelope F c r ρ x ∂μ) ≤
      ENNReal.ofReal ((Real.pi * (ρ - r) ^ 2)⁻¹) * ENNReal.ofReal C * volume (ball c ρ) := by
  have hg : Measurable (fun q : α × ℂ => ENNReal.ofReal (‖F q.1 q.2‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hF.norm.pow_const 2)
  have hinner : Measurable (fun x : α => ∫⁻ z in ball c ρ, ENNReal.ofReal (‖F x z‖ ^ 2)) :=
    hg.lintegral_prod_right'
  unfold compactDiscMeanSqEnvelope
  rw [lintegral_const_mul _ hinner, lintegral_lintegral_swap hg.aemeasurable]
  calc
    _ ≤ ENNReal.ofReal ((Real.pi * (ρ - r) ^ 2)⁻¹) *
        ∫⁻ _z in ball c ρ, ENNReal.ofReal C := by
      apply mul_le_mul_right
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      exact hbound z hz
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_assoc]

end RHTower
