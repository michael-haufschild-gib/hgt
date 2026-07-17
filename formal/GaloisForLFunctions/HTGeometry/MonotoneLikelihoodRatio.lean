import Mathlib.MeasureTheory.Integral.Prod

/-!
# Monotone-likelihood kernels and normalized expectation order

This file contains the measure-theoretic integration step behind the monotone-likelihood-ratio
order.  It is independent of zeta, theta functions, and any particular hypertranscendental
source.  If two positive component densities have a two-sample kernel with the same sign as an
observable increment, product integration turns that pointwise sign into the corresponding
cross-multiplied normalized expectation order.

The theorem is deliberately stated in division-free form.  It remains useful when masses are
known to be finite but positivity needed for normalization is proved only at a later consumer.
-/

open MeasureTheory

namespace HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Integrated monotone-likelihood kernel.**  If the two-sample kernel

`(g(y)-g(x)) * (h(x)*f(y)-h(y)*f(x))`

is almost everywhere nonnegative, then the `g`-moment of `h`, normalized by the mass of `h`, is
at most the corresponding normalized value for `f`.  The conclusion is cross-multiplied, so no
nonzero-mass hypothesis is needed. -/
theorem integral_mul_integral_le_of_monotoneLikelihoodKernel
    [SFinite μ] {f h g : α → ℝ}
    (hf : Integrable f μ) (hh : Integrable h μ)
    (hgf : Integrable (fun x => g x * f x) μ)
    (hgh : Integrable (fun x => g x * h x) μ)
    (hkernel : ∀ᵐ z : α × α ∂μ.prod μ,
      0 ≤ (g z.2 - g z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1)) :
    (∫ x, g x * h x ∂μ) * (∫ x, f x ∂μ) ≤
      (∫ x, g x * f x ∂μ) * (∫ x, h x ∂μ) := by
  let K : α × α → ℝ := fun z =>
    (g z.2 - g z.1) * (h z.1 * f z.2 - h z.2 * f z.1)
  let T₁ : α × α → ℝ := fun z => h z.1 * (g z.2 * f z.2)
  let T₂ : α × α → ℝ := fun z => f z.1 * (g z.2 * h z.2)
  let T₃ : α × α → ℝ := fun z => (g z.1 * h z.1) * f z.2
  let T₄ : α × α → ℝ := fun z => (g z.1 * f z.1) * h z.2
  have hT₁ : Integrable T₁ (μ.prod μ) := by
    simpa only [T₁] using hh.mul_prod hgf
  have hT₂ : Integrable T₂ (μ.prod μ) := by
    simpa only [T₂] using hf.mul_prod hgh
  have hT₃ : Integrable T₃ (μ.prod μ) := by
    simpa only [T₃] using hgh.mul_prod hf
  have hT₄ : Integrable T₄ (μ.prod μ) := by
    simpa only [T₄] using hgf.mul_prod hh
  have hKexpand : K = T₁ - T₂ - T₃ + T₄ := by
    funext z
    simp only [K, T₁, T₂, T₃, T₄, Pi.add_apply, Pi.sub_apply]
    ring
  have hKint : Integrable K (μ.prod μ) := by
    rw [hKexpand]
    exact ((hT₁.sub hT₂).sub hT₃).add hT₄
  have hKnonneg : 0 ≤ ∫ z, K z ∂μ.prod μ := by
    apply integral_nonneg_of_ae
    simpa only [K] using hkernel
  have hT₁value :
      (∫ z : α × α, h z.1 * (g z.2 * f z.2) ∂μ.prod μ) =
        (∫ x, h x ∂μ) * ∫ x, g x * f x ∂μ :=
    integral_prod_mul h (fun x => g x * f x)
  have hT₂value :
      (∫ z : α × α, f z.1 * (g z.2 * h z.2) ∂μ.prod μ) =
        (∫ x, f x ∂μ) * ∫ x, g x * h x ∂μ :=
    integral_prod_mul f (fun x => g x * h x)
  have hT₃value :
      (∫ z : α × α, (g z.1 * h z.1) * f z.2 ∂μ.prod μ) =
        (∫ x, g x * h x ∂μ) * ∫ x, f x ∂μ :=
    integral_prod_mul (fun x => g x * h x) f
  have hT₄value :
      (∫ z : α × α, (g z.1 * f z.1) * h z.2 ∂μ.prod μ) =
        (∫ x, g x * f x ∂μ) * ∫ x, h x ∂μ :=
    integral_prod_mul (fun x => g x * f x) h
  have hKvalue :
      (∫ z, K z ∂μ.prod μ) =
        2 * ((∫ x, g x * f x ∂μ) * (∫ x, h x ∂μ) -
          (∫ x, g x * h x ∂μ) * (∫ x, f x ∂μ)) := by
    rw [hKexpand, integral_add' ((hT₁.sub hT₂).sub hT₃) hT₄,
      integral_sub' (hT₁.sub hT₂) hT₃, integral_sub' hT₁ hT₂]
    simp only [T₁, T₂, T₃, T₄]
    rw [hT₁value, hT₂value, hT₃value, hT₄value]
    ring
  rw [hKvalue] at hKnonneg
  nlinarith

end
end HTGeometry
