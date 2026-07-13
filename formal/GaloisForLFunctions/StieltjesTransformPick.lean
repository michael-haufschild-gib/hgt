import Mathlib

/-!
# The Stieltjes transform of a positive measure is a Pick function

The analytic bridge between the moment problem and Nevanlinna–Pick theory, absent from mathlib as a
packaged statement.  For a positive measure `μ` on `ℝ`, its **Stieltjes/Cauchy transform**

`S_μ(z) = ∫ (x − z)⁻¹ dμ(x)`

maps the open upper half-plane into the closed upper half-plane, and into the open upper half-plane
when `μ ≠ 0` — it is a **Pick (Herglotz/Nevanlinna) function**.  The mechanism is the pointwise
positivity of the imaginary part of the Cauchy kernel,

`Im (x − z)⁻¹ = Im z / |x − z|²  ≥ 0   (> 0 when Im z > 0)`,

combined with commuting `Im` through the Bochner integral.  This Herglotz positivity is the load-bearing
analytic input of the Nevanlinna-parametrization and Pick-defect cards
(`nevanlinna-boundary-bauer-retract-maximal-ht`, `pick-defect-finite-selector-maximal-ht-phase-law`):
every representing measure of an indeterminate moment sequence produces, through `S_μ`, a Pick function
whose boundary behaviour carries the moment data.
-/

open scoped BigOperators
open MeasureTheory Complex

namespace HTGeometry

/-- The imaginary part of the Cauchy kernel at a real point: `Im (x − z)⁻¹ = Im z / |x − z|²`. -/
theorem cauchyKernel_im (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = z.im / Complex.normSq ((x : ℂ) - z) := by
  rw [Complex.inv_im]
  simp [Complex.sub_im, Complex.ofReal_im]

/-- Commuting the imaginary part through the Bochner integral of an integrable complex function. -/
theorem im_integral {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := by
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hf]
  rfl

/-- **Herglotz positivity (closed half-plane).**  The Stieltjes transform of a positive measure has
nonnegative imaginary part throughout the closed upper half-plane. -/
theorem stieltjesTransform_im_nonneg {μ : Measure ℝ} (z : ℂ) (hz : 0 ≤ z.im)
    (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    0 ≤ (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  rw [im_integral hInt]
  refine integral_nonneg (fun x => ?_)
  rw [cauchyKernel_im x z]
  exact div_nonneg hz (Complex.normSq_nonneg _)

/-- The imaginary part of the Cauchy kernel is strictly positive in the open upper half-plane. -/
theorem cauchyKernel_im_pos (x : ℝ) (z : ℂ) (hz : 0 < z.im) :
    0 < (((x : ℂ) - z)⁻¹).im := by
  rw [cauchyKernel_im x z]
  refine div_pos hz ?_
  rw [Complex.normSq_pos]
  intro hzero
  have hzx : z = (x : ℂ) := by
    have := sub_eq_zero.mp hzero
    exact this.symm
  rw [hzx] at hz
  simp [Complex.ofReal_im] at hz

/-- **Pick property (open half-plane).**  The Stieltjes transform of a nonzero positive measure has
strictly positive imaginary part everywhere in the open upper half-plane: `S_μ` is a Pick function. -/
theorem stieltjesTransform_im_pos {μ : Measure ℝ} (z : ℂ) (hz : 0 < z.im)
    (hμ : 0 < μ Set.univ) (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  rw [im_integral hInt]
  have hIntIm : Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) μ := hInt.im
  rw [integral_pos_iff_support_of_nonneg (fun x => (cauchyKernel_im_pos x z hz).le) hIntIm]
  have hsupp : Function.support (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (cauchyKernel_im_pos x z hz)
  rw [hsupp]
  exact hμ

end HTGeometry
