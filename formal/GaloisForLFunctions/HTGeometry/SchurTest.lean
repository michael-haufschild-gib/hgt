import GaloisForLFunctions.HTGeometry.MinkowskiIntegralInequality

/-!
# Schur's test

A kernel with uniformly bounded rows and columns is bounded on `L²`, with norm at most the geometric
mean of the two bounds:

`∫ K(x,η)dη ≤ A`,  `∫ K(x,η)dx ≤ B`  ⟹  `‖Kf‖₂² ≤ A·B·‖f‖₂²`.

The proof splits the kernel as `K^{1/2}·K^{1/2}`, applies Cauchy–Schwarz in the integration variable
to pay for the row bound, and then exchanges the two integrations to pay for the column bound.
Stated in `ℝ≥0∞`, so nothing beyond measurability of the kernel is required.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

omit [MeasurableSpace α] in
/-- **The row step.**  Cauchy–Schwarz against the square root of the kernel. -/
theorem sq_lintegral_kernel_le {K : α → β → ℝ≥0∞} {f : β → ℝ≥0∞} {A : ℝ≥0∞}
    (hK : ∀ x, AEMeasurable (K x) ν) (hf : AEMeasurable f ν)
    (hrow : ∀ x, (∫⁻ η, K x η ∂ν) ≤ A) (x : α) :
    (∫⁻ η, K x η * f η ∂ν) ^ 2 ≤ A * ∫⁻ η, K x η * f η ^ 2 ∂ν := by
  have hhalf : ∀ η : β, (K x η) ^ ((1 : ℝ) / 2) * ((K x η) ^ ((1 : ℝ) / 2) * f η)
      = K x η * f η := by
    intro η
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hmeas₁ : AEMeasurable (fun η => (K x η) ^ ((1 : ℝ) / 2)) ν := (hK x).pow_const _
  have hmeas₂ : AEMeasurable (fun η => (K x η) ^ ((1 : ℝ) / 2) * f η) ν := hmeas₁.mul hf
  have hCS := lintegral_mul_le_sqrt_mul_sqrt (μ := ν) hmeas₁ hmeas₂
  have hcongr : (∫⁻ η, (K x η) ^ ((1 : ℝ) / 2) * ((K x η) ^ ((1 : ℝ) / 2) * f η) ∂ν)
      = ∫⁻ η, K x η * f η ∂ν := lintegral_congr fun η => hhalf η
  rw [hcongr] at hCS
  have hsq₁ : ∀ η : β, ((K x η) ^ ((1 : ℝ) / 2)) ^ 2 = K x η := by
    intro η
    rw [← ENNReal.rpow_natCast ((K x η) ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have hsq₂ : ∀ η : β, ((K x η) ^ ((1 : ℝ) / 2) * f η) ^ 2 = K x η * f η ^ 2 := by
    intro η
    rw [mul_pow, hsq₁ η]
  have hprod : ((∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2)) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)
      * (∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2) * f η) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)) ^ 2
      = (∫⁻ η, K x η ∂ν) * ∫⁻ η, K x η * f η ^ 2 ∂ν := by
    rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2)) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)) 2,
      ← ENNReal.rpow_natCast ((∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2) * f η) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)) 2,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    norm_num
    rw [lintegral_congr fun η => hsq₁ η, lintegral_congr fun η => hsq₂ η]
  calc (∫⁻ η, K x η * f η ∂ν) ^ 2
      ≤ ((∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2)) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)
          * (∫⁻ η, ((K x η) ^ ((1 : ℝ) / 2) * f η) ^ 2 ∂ν) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' hCS 2
    _ = (∫⁻ η, K x η ∂ν) * ∫⁻ η, K x η * f η ^ 2 ∂ν := hprod
    _ ≤ A * ∫⁻ η, K x η * f η ^ 2 ∂ν := mul_le_mul' (hrow x) le_rfl

/-- **Schur's test.** -/
theorem lintegral_sq_kernel_le [SFinite μ] [SFinite ν] {K : α → β → ℝ≥0∞} {f : β → ℝ≥0∞}
    {A B : ℝ≥0∞} (hKmeas : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, (∫⁻ η, K x η ∂ν) ≤ A) (hcol : ∀ η, (∫⁻ x, K x η ∂μ) ≤ B) :
    (∫⁻ x, (∫⁻ η, K x η * f η ∂ν) ^ 2 ∂μ) ≤ A * B * ∫⁻ η, f η ^ 2 ∂ν := by
  have hKx : ∀ x, AEMeasurable (K x) ν := fun x =>
    (hKmeas.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hstep : (∫⁻ x, (∫⁻ η, K x η * f η ∂ν) ^ 2 ∂μ)
      ≤ ∫⁻ x, A * ∫⁻ η, K x η * f η ^ 2 ∂ν ∂μ :=
    lintegral_mono fun x => sq_lintegral_kernel_le hKx hf.aemeasurable hrow x
  have hswap : (∫⁻ x, ∫⁻ η, K x η * f η ^ 2 ∂ν ∂μ)
      = ∫⁻ η, ∫⁻ x, K x η * f η ^ 2 ∂μ ∂ν := by
    refine lintegral_lintegral_swap ?_
    exact (hKmeas.mul ((hf.pow_const 2).comp measurable_snd)).aemeasurable
  have hcolstep : (∫⁻ η, ∫⁻ x, K x η * f η ^ 2 ∂μ ∂ν) ≤ B * ∫⁻ η, f η ^ 2 ∂ν := by
    have hinner : ∀ η, (∫⁻ x, K x η * f η ^ 2 ∂μ) ≤ B * f η ^ 2 := by
      intro η
      have hmK : Measurable fun x => K x η :=
        hKmeas.comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hmK]
      exact mul_le_mul' (hcol η) le_rfl
    calc (∫⁻ η, ∫⁻ x, K x η * f η ^ 2 ∂μ ∂ν)
        ≤ ∫⁻ η, B * f η ^ 2 ∂ν := lintegral_mono hinner
      _ = B * ∫⁻ η, f η ^ 2 ∂ν := lintegral_const_mul _ (hf.pow_const 2)
  calc (∫⁻ x, (∫⁻ η, K x η * f η ∂ν) ^ 2 ∂μ)
      ≤ ∫⁻ x, A * ∫⁻ η, K x η * f η ^ 2 ∂ν ∂μ := hstep
    _ = A * ∫⁻ x, ∫⁻ η, K x η * f η ^ 2 ∂ν ∂μ :=
        lintegral_const_mul _ (hKmeas.mul ((hf.pow_const 2).comp measurable_snd)).lintegral_prod_right'
    _ = A * ∫⁻ η, ∫⁻ x, K x η * f η ^ 2 ∂μ ∂ν := by rw [hswap]
    _ ≤ A * (B * ∫⁻ η, f η ^ 2 ∂ν) := mul_le_mul' le_rfl hcolstep
    _ = A * B * ∫⁻ η, f η ^ 2 ∂ν := by rw [mul_assoc]

end GaloisForLFunctions.HTGeometry
