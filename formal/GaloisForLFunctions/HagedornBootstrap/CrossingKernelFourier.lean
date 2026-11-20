import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion

/-!
# The crossing kernel is a Gaussian minus its own Fourier transform

Read the dimension variable as `t = |r|²/2` for a point `r` of a Euclidean space `V` of dimension
`d`. The modular crossing kernel of the spinless bootstrap (and, with `d = 2c`, of its `U(1)^c`
twin) becomes

  `Ξ_β(v) = e^{−πβ‖v‖²} − β^{−d/2} e^{−π‖v‖²/β}`,

a Gaussian minus its own Fourier transform. Since the Fourier transform maps `e^{−πβ‖v‖²}` to
`β^{−d/2} e^{−π‖w‖²/β}`, one gets `𝓕 Ξ_β = −Ξ_β`: every linear functional of the crossing
equation is a `−1` eigenfunction of the Fourier transform, and `β` drops out of the problem.

For any integrable `−1` eigenfunction `f`, evaluating at the origin gives `f(0) = −∫ f`: a
functional that is nonnegative everywhere has `f(0) ≤ 0`, so no functional certifies a gap at the
origin. Conversely, in the Cohn–Elkies dictionary, for continuous `h` with `𝓕(𝓕h) = h` the function
`f = 𝓕h − h` is a `−1` eigenfunction.
-/

noncomputable section

open Real Complex MeasureTheory FourierTransform
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HagedornBootstrap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian `e^{−πβ‖v‖²}`. -/
def gaussianB (β : ℝ) (v : V) : ℂ := cexp (-((π * β : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2)

/-- The scale factor `β^{−d/2}`. -/
def gaussScale (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (β : ℝ) : ℂ :=
  ((β ^ (-((Module.finrank ℝ V : ℝ) / 2)) : ℝ) : ℂ)

theorem integrable_gaussianB {β : ℝ} (hβ : 0 < β) : Integrable (gaussianB (V := V) β) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := ((π * β : ℝ) : ℂ))
    (by simp only [ofReal_re]; positivity) 0 0
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp [gaussianB]

/-- **Fourier transform of the Gaussian:** `𝓕 e^{−πβ‖·‖²} = β^{−d/2} e^{−π‖·‖²/β}`. -/
theorem fourier_gaussianB {β : ℝ} (hβ : 0 < β) (w : V) :
    𝓕 (gaussianB (V := V) β) w = gaussScale V β * gaussianB β⁻¹ w := by
  have h := fourier_gaussian_innerProductSpace (V := V) (b := ((π * β : ℝ) : ℂ))
    (by simp only [ofReal_re]; positivity) w
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hβ0 : β ≠ 0 := hβ.ne'
  unfold gaussianB
  rw [h]
  unfold gaussScale
  congr 1
  · rw [show (π : ℂ) / ((π * β : ℝ) : ℂ) = ((β⁻¹ : ℝ) : ℂ) by push_cast; field_simp]
    rw [← Complex.ofReal_natCast, show ((Module.finrank ℝ V : ℝ) : ℂ) / 2 =
      (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), Real.inv_rpow hβ.le, ← Real.rpow_neg hβ.le]
  · congr 1
    push_cast
    field_simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem gaussScale_mul_inv {β : ℝ} (hβ : 0 < β) : gaussScale V β * gaussScale V β⁻¹ = 1 := by
  unfold gaussScale
  rw [← Complex.ofReal_mul, Real.inv_rpow hβ.le, ← Real.rpow_neg hβ.le,
    ← Real.rpow_add hβ, neg_neg, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]

/-- The Fourier transform is linear on integrable functions. -/
theorem fourier_sub_const_mul {f g : V → ℂ} (hf : Integrable f) (hg : Integrable g) (c : ℂ) (w : V) :
    𝓕 (fun v => f v - c * g v) w = 𝓕 f w - c * 𝓕 g w := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  have h1 : Integrable (fun v => 𝐞 (-⟪v, w⟫) • f v) := (Real.fourierIntegral_convergent_iff w).2 hf
  have h2 : Integrable (fun v => 𝐞 (-⟪v, w⟫) • g v) := (Real.fourierIntegral_convergent_iff w).2 hg
  rw [← integral_const_mul, ← integral_sub h1 (h2.const_mul c)]
  congr 1; funext v
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- The crossing kernel `Ξ_β = e^{−πβ‖·‖²} − β^{−d/2} e^{−π‖·‖²/β}`. -/
def crossingKernel (β : ℝ) (v : V) : ℂ := gaussianB β v - gaussScale V β * gaussianB β⁻¹ v

/-- **The crossing kernel is a `−1` eigenfunction of the Fourier transform.** -/
theorem fourier_crossingKernel {β : ℝ} (hβ : 0 < β) :
    𝓕 (crossingKernel (V := V) β) = fun w => -crossingKernel β w := by
  funext w
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  unfold crossingKernel
  rw [fourier_sub_const_mul (integrable_gaussianB hβ) (integrable_gaussianB hb), fourier_gaussianB hβ,
    fourier_gaussianB hb, inv_inv, ← mul_assoc, gaussScale_mul_inv hβ]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- At `β = 1` the Gaussian is self-dual and the crossing kernel vanishes. -/
theorem crossingKernel_one : crossingKernel (V := V) 1 = 0 := by
  funext v
  simp [crossingKernel, gaussScale]

/-- The value at the origin of a Fourier transform is the integral. -/
theorem fourier_zero_eq_integral (f : V → ℂ) : 𝓕 f 0 = ∫ v, f v := by
  rw [Real.fourier_eq]
  simp

/-- **A `−1` eigenfunction is minus its integral at the origin:** `f(0) = −∫ f`. -/
theorem eigen_neg_value_at_zero {f : V → ℂ} (hf : 𝓕 f = fun w => -f w) : f 0 = -∫ v, f v := by
  have h := fourier_zero_eq_integral f
  rw [hf] at h
  linear_combination -h

/-- **No gap at the origin.** A `−1` eigenfunction with nonnegative real part has
`Re f(0) ≤ 0`. -/
theorem eigen_neg_re_zero_nonpos {f : V → ℂ} (hf : 𝓕 f = fun w => -f w)
    (hint : Integrable f) (hpos : ∀ v, 0 ≤ (f v).re) : (f 0).re ≤ 0 := by
  rw [eigen_neg_value_at_zero hf, neg_re]
  have h2 : (∫ v, f v).re = ∫ v, (f v).re := (integral_re hint).symm
  have : 0 ≤ ∫ v, (f v).re := integral_nonneg hpos
  linarith

/-- **Cohn–Elkies dictionary.** If `h` is continuous and integrable with integrable transform and
`𝓕(𝓕h) = h` (e.g. `h` even), then `f = 𝓕h − h` is a `−1` eigenfunction. -/
theorem fourier_sub_self_eigen {h : V → ℂ} (hh : Integrable h) (hFh : Integrable (𝓕 h))
    (hinv : 𝓕 (𝓕 h) = h) : 𝓕 (fun v => 𝓕 h v - 1 * h v) = fun w => -(𝓕 h w - 1 * h w) := by
  funext w
  rw [fourier_sub_const_mul hFh hh, hinv]
  ring

end GaloisForLFunctions.HagedornBootstrap
