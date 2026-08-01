import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Fourier integral under a dilation of the line

Precomposing with a dilation of the line rescales the Fourier integral: the transform of
`x ↦ f (x / δ)` at `ξ` is `δ` times the transform of `f` at `δ ξ`.

Mathlib has the translation and isometry rules for the Fourier integral but not this one, so it is
proved here by substituting the dilation in the defining integral.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Dilation rule for the Fourier integral.** -/
theorem fourierIntegral_comp_div (f : ℝ → E) (δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f (x / δ)) ξ = δ • 𝓕 f (δ * ξ) := by
  have hpoint : ∀ x : ℝ,
      Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) • f (x / δ) =
        (fun y : ℝ => Complex.exp ((↑(-2 * π * y * (δ * ξ)) : ℂ) * Complex.I) • f y) (x / δ) := by
    intro x
    have hδ0 : δ ≠ 0 := hδ.ne'
    have harg : -2 * π * (x / δ) * (δ * ξ) = -2 * π * x * ξ := by
      field_simp
    show Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) • f (x / δ) =
      Complex.exp ((↑(-2 * π * (x / δ) * (δ * ξ)) : ℂ) * Complex.I) • f (x / δ)
    rw [harg]
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => Complex.exp ((↑(-2 * π * y * (δ * ξ)) : ℂ) * Complex.I) • f y) δ,
    abs_of_pos hδ]

/-- **Additivity of the Fourier integral on the line.**  Mathlib carries additivity only in the
abstract bilinear form, with continuity side conditions; this is the specialisation to `ℝ`. -/
theorem fourierIntegral_add {f g : ℝ → E} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f x + g x) ξ = 𝓕 f ξ + 𝓕 g ξ := by
  have hinner : ∀ a : ℝ, (inner ℝ a ξ : ℝ) = a * ξ := fun a => Real.inner_apply a ξ
  have h1 := (Real.fourierIntegral_convergent_iff (f := f) ξ).2 hf
  have h2 := (Real.fourierIntegral_convergent_iff (f := g) ξ).2 hg
  simp only [hinner] at h1 h2
  rw [Real.fourier_real_eq, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_add h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [smul_add]

/-- **Translation rule for the Fourier integral on the line.**  Right translation contributes a
unimodular phase. -/
theorem fourierIntegral_comp_add_right (f : ℝ → E) (a : ℝ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => f (x + a)) ξ =
      Complex.exp ((↑(2 * π * a * ξ) : ℂ) * Complex.I) • 𝓕 f ξ := by
  have hshift := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun u : ℝ => Complex.exp ((↑(-2 * π * (u - a) * ξ) : ℂ) * Complex.I) • f u) a
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hleft : ∀ v : ℝ, Complex.exp ((↑(-2 * π * v * ξ) : ℂ) * Complex.I) • f (v + a) =
      (fun u : ℝ => Complex.exp ((↑(-2 * π * (u - a) * ξ) : ℂ) * Complex.I) • f u) (v + a) := by
    intro v
    congr 2
    push_cast
    ring_nf
  rw [integral_congr_ae (Filter.Eventually.of_forall hleft), hshift, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show Complex.exp ((↑(-2 * π * (u - a) * ξ) : ℂ) * Complex.I) • f u =
    Complex.exp ((↑(2 * π * a * ξ) : ℂ) * Complex.I) •
      Complex.exp ((↑(-2 * π * u * ξ) : ℂ) * Complex.I) • f u
  rw [smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Multiplying by a unimodular character preserves integrability. -/
theorem integrable_exp_mul {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable fun x : ℝ => Complex.exp ((↑(2 * π * a * x) : ℂ) * Complex.I) * f x := by
  refine hf.bdd_mul (c := 1) ?_ ?_
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).aestronglyMeasurable
  · filter_upwards with x
    rw [Complex.norm_exp]
    have harg : ((↑(2 * π * a * x) : ℂ) * Complex.I).re = 0 := by simp
    rw [harg, Real.exp_zero]

/-- **Scalar rule.**  The Fourier integral is homogeneous. -/
theorem fourierIntegral_const_mul (f : ℝ → ℂ) (r : ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => r * f x) ξ = r * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) • (r * f x) =
    r * (Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) • f x)
  rw [smul_eq_mul, smul_eq_mul]
  ring

/-- **Modulation rule.**  Multiplying by a character shifts the transform. -/
theorem fourierIntegral_exp_mul (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp ((↑(2 * π * a * x) : ℂ) * Complex.I) * f x) ξ =
      𝓕 f (ξ - a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp ((↑(-2 * π * x * ξ) : ℂ) * Complex.I) •
      (Complex.exp ((↑(2 * π * a * x) : ℂ) * Complex.I) * f x) =
    Complex.exp ((↑(-2 * π * x * (ξ - a)) : ℂ) * Complex.I) • f x
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, ← add_mul]
  congr 3
  push_cast
  ring

/-- **The cosine modulation rule.**  Multiplying by a real cosine splits the transform into the
average of two shifts. -/
theorem fourierIntegral_mul_cos {f : ℝ → ℂ} (hf : Integrable f) (w₀ ξ : ℝ) :
    𝓕 (fun x : ℝ => f x * ((Real.cos (2 * π * w₀ * x) : ℝ) : ℂ)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 f (ξ - w₀) + (2 : ℂ)⁻¹ * 𝓕 f (ξ + w₀) := by
  have hplus := integrable_exp_mul hf w₀
  have hminus := integrable_exp_mul hf (-w₀)
  have hsplit : (fun x : ℝ => f x * ((Real.cos (2 * π * w₀ * x) : ℝ) : ℂ)) =
      fun x : ℝ =>
        (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * π * w₀ * x) : ℂ) * Complex.I) * f x) +
          (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * π * -w₀ * x) : ℂ) * Complex.I) * f x) := by
    funext x
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hsplit, fourierIntegral_add (hplus.const_mul _) (hminus.const_mul _) ξ,
    fourierIntegral_const_mul _ (2 : ℂ)⁻¹ ξ, fourierIntegral_const_mul _ (2 : ℂ)⁻¹ ξ,
    fourierIntegral_exp_mul f w₀ ξ, fourierIntegral_exp_mul f (-w₀) ξ, sub_neg_eq_add]

end GaloisForLFunctions.HTGeometry
