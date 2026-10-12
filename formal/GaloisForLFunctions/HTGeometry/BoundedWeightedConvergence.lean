import GaloisForLFunctions.HTGeometry.IntegralVariableDomination
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted

/-! Bounded continuous observations commute with converging nonnegative weights. -/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

theorem integral_tilted_real_eq_ratio {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q f : α → ℝ) :
    (∫ x, f x ∂(μ.tilted q)) =
      (∫ x, Real.exp (q x) * f x ∂μ) / ∫ x, Real.exp (q x) ∂μ := by
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have h : (fun x => (Real.exp (q x) / ∫ y, Real.exp (q y) ∂μ) * f x) =
      (fun x => (Real.exp (q x) * f x) * (∫ y, Real.exp (q y) ∂μ)⁻¹) := by
    funext x
    ring
  rw [h, integral_mul_const, div_eq_mul_inv]

theorem tendsto_integral_weighted_boundedContinuousFunction
    {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace β] [OpensMeasurableSpace β] {μ : Measure α}
    {l : Filter ι} [l.IsCountablyGenerated] {Xn : ι → α → β} {X : α → β}
    {wn : ι → α → ℝ} {w : α → ℝ}
    (hXn : ∀ i, Measurable (Xn i)) (hX : Measurable X)
    (hwi : ∀ i, Integrable (wn i) μ) (hw : Integrable w μ)
    (hwnn : ∀ i, 0 ≤ᵐ[μ] wn i) (hwn : 0 ≤ᵐ[μ] w)
    (hXt : ∀ᵐ x ∂μ, Tendsto (fun i => Xn i x) l (𝓝 (X x)))
    (hwt : ∀ᵐ x ∂μ, Tendsto (fun i => wn i x) l (𝓝 (w x)))
    (hI : Tendsto (fun i => ∫ x, wn i x ∂μ) l (𝓝 (∫ x, w x ∂μ)))
    (f : BoundedContinuousFunction β ℝ) :
    Tendsto (fun i => ∫ x, wn i x * f (Xn i x) ∂μ) l
      (𝓝 (∫ x, w x * f (X x) ∂μ)) := by
  have hbound (i : ι) : ∀ᵐ x ∂μ, ‖wn i x * f (Xn i x)‖ ≤ ‖f‖ * wn i x := by
    filter_upwards [hwnn i] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx]
    exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) hx).trans_eq (mul_comm _ _)
  have hbound' : ∀ᵐ x ∂μ, ‖w x * f (X x)‖ ≤ ‖f‖ * w x := by
    filter_upwards [hwn] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hx]
    exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) hx).trans_eq (mul_comm _ _)
  have hfi (i : ι) : Integrable (fun x => wn i x * f (Xn i x)) μ :=
    ((hwi i).const_mul ‖f‖).mono'
      ((hwi i).aestronglyMeasurable.mul
        (f.continuous.measurable.comp (hXn i)).aestronglyMeasurable) (hbound i)
  have hFi : Integrable (fun x => w x * f (X x)) μ :=
    (hw.const_mul ‖f‖).mono'
      (hw.aestronglyMeasurable.mul (f.continuous.measurable.comp hX).aestronglyMeasurable) hbound'
  apply tendsto_integral_of_variable_envelope hfi hFi hbound
    (fun i => (hwi i).const_mul ‖f‖) (hw.const_mul ‖f‖)
  · exact hwn.mono fun _ hx => mul_nonneg (norm_nonneg _) hx
  · filter_upwards [hXt, hwt] with x hXx hwx
    exact hwx.mul (f.continuous.continuousAt.tendsto.comp hXx)
  · exact hwt.mono fun _ hx => hx.const_mul ‖f‖
  · simp_rw [integral_const_mul]
    exact hI.const_mul ‖f‖

end GaloisForLFunctions.HTGeometry
