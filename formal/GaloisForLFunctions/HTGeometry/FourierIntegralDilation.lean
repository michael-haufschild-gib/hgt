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

end GaloisForLFunctions.HTGeometry
