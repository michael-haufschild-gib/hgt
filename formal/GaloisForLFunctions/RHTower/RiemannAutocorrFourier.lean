import GaloisForLFunctions.RHTower.WeilDeviationTranslationBound
import GaloisForLFunctions.RHTower.XiRealZeroFejerSum
import GaloisForLFunctions.RHTower.HodgeNyquistExclusion
import GaloisForLFunctions.RHTower.XiEntireReal
import Mathlib.Analysis.Fourier.Convolution

/-!
# The Fourier transform of Riemann's autocorrelation is `Ξ²`

Let `Φ` be Riemann's kernel and `K(y) = ∫ Φ(t) Φ(t − y) dt` its autocorrelation. With Mathlib's
transform `𝓕 f (ξ) = ∫ e^{−2πiξx} f(x) dx`:
- `𝓕Φ(ξ) = XiC(2πξ) = ξ(1/2 + 2πiξ)`, which is real (`riemannXi_eq_XiC`);
- `𝓕K = (𝓕Φ)²`, since `Φ` is even and `K = Φ ⋆ Φ` (`fourier_riemannAutocorr`).

Hence the real zeros of `𝓕K` are the ordinates of the zeros of `ζ` on the critical line, divided by
`2π`. The frequency function `riemannXi` is smooth, since `XiC` is entire.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate Convolution ContDiff

namespace RHTower.WeilExcess

noncomputable section

theorem riemannKernelReal_neg (u : ℝ) : riemannKernelReal (-u) = riemannKernelReal u := by
  simp [riemannKernelReal, abs_neg]

/-- Riemann's kernel as a complex function. -/
def riemannKernelC (x : ℝ) : ℂ := (riemannKernelReal x : ℂ)

theorem integrable_riemannKernelReal : Integrable riemannKernelReal := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul C)
    continuous_riemannKernelReal.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have h := hC x
  rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, one_mul] at h
  rw [Real.norm_eq_abs]
  exact h

theorem integrable_riemannKernelC : Integrable riemannKernelC :=
  integrable_riemannKernelReal.ofReal

theorem riemannAutocorr_eq_convolution (y : ℝ) :
    ((riemannAutocorr y : ℝ) : ℂ) =
      (riemannKernelC ⋆[ContinuousLinearMap.mul ℂ ℂ] riemannKernelC) y := by
  rw [convolution_def, riemannAutocorr, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', riemannKernelC]
  rw [show y - t = -(t - y) by ring, riemannKernelReal_neg]
  push_cast; ring

/-- `Ξ` on the frequency line: `𝓕Φ(ξ)`. -/
def riemannXi (ξ : ℝ) : ℂ := 𝓕 riemannKernelC ξ

/-- **`𝓕K = Ξ²`.** -/
theorem fourier_riemannAutocorr (ξ : ℝ) :
    𝓕 (fun y => ((riemannAutocorr y : ℝ) : ℂ)) ξ = riemannXi ξ ^ 2 := by
  have h : (fun y => ((riemannAutocorr y : ℝ) : ℂ)) =
      riemannKernelC ⋆[ContinuousLinearMap.mul ℂ ℂ] riemannKernelC :=
    funext riemannAutocorr_eq_convolution
  rw [h, Real.fourier_mul_convolution_eq integrable_riemannKernelC integrable_riemannKernelC, sq]
  rfl

/-- The transform as an explicit integral. -/
theorem fourier_eq_integral (h : ℝ → ℂ) (u : ℝ) :
    𝓕 h u = ∫ ξ, Complex.exp (-(2 * π * ξ * u : ℝ) * I) * h ξ := by
  rw [Real.fourier_real_eq]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 2
  push_cast; ring

/-- **`𝓕Φ(ξ) = XiC(2πξ)`.** -/
theorem riemannXi_eq_XiC (ξ : ℝ) : riemannXi ξ = XiC (2 * π * ξ) := by
  have h1 := paperFT_riemannPhiKernel (-(2 * π * ξ : ℂ))
  rw [riemannPhiTransform_eq_xi] at h1
  have h2 : xi (1 / 2 + I * -(2 * π * ξ : ℂ)) = XiC (2 * π * ξ) := by
    rw [← XiC_even]; unfold XiC; congr 1; ring
  rw [h2] at h1
  rw [← h1, riemannXi, fourier_eq_integral]
  unfold Zeta23.paperFT
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [riemannPhiKernel_eq_ofReal, riemannKernelC]
  rw [mul_comm]
  congr 2
  push_cast; ring

theorem riemannXi_im (ξ : ℝ) : (riemannXi ξ).im = 0 := by
  rw [riemannXi_eq_XiC, show (2 * π * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) by push_cast; ring]
  exact XiC_ofReal_im (2 * π * ξ)

/-- `Ξ` as a real function on the frequency line. -/
def riemannXiReal (ξ : ℝ) : ℝ := (riemannXi ξ).re

theorem riemannXi_eq_ofReal (ξ : ℝ) : riemannXi ξ = (riemannXiReal ξ : ℂ) :=
  Complex.ext (by simp [riemannXiReal]) (by simp [riemannXi_im])

theorem contDiff_riemannXi : ContDiff ℝ ∞ riemannXi := by
  have h1 : ContDiff ℂ ∞ XiC := XiC_differentiable.contDiff
  have h2 : ContDiff ℝ ∞ (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)
  have h3 := (h1.restrict_scalars ℝ).comp h2
  have e : riemannXi = XiC ∘ (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) := by
    funext ξ
    simp only [Function.comp, riemannXi_eq_XiC]
    push_cast; ring_nf
  rw [e]; exact h3

theorem contDiff_riemannXiReal : ContDiff ℝ ∞ riemannXiReal :=
  Complex.reCLM.contDiff.comp contDiff_riemannXi

theorem riemannXi_eq_zero_iff (ξ : ℝ) : riemannXi ξ = 0 ↔ XiC ((2 * π * ξ : ℝ) : ℂ) = 0 := by
  rw [riemannXi_eq_XiC]; push_cast; rfl

theorem riemannXiReal_eq_zero_iff (ξ : ℝ) :
    riemannXiReal ξ = 0 ↔ XiC ((2 * π * ξ : ℝ) : ℂ) = 0 := by
  rw [← riemannXi_eq_zero_iff, riemannXi_eq_ofReal, Complex.ofReal_eq_zero]

theorem riemannXiReal_zero_ne : riemannXiReal 0 ≠ 0 := by
  rw [Ne, riemannXiReal_eq_zero_iff]
  have h : XiC (((2 * π * 0 : ℝ)) : ℂ) = xi (1 / 2) := by unfold XiC; congr 1; push_cast; ring
  rw [h]
  intro h0
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (0 : ℂ)).mp
    (by unfold XiC; simpa using h0)
  have := four_half_lt_abs_im_of_xiZeroCopy q
  rw [xiZeroCopy_eq_half_add_of_spectral (t := 0) (by simpa using hq)] at this
  norm_num at this

end

end RHTower.WeilExcess
