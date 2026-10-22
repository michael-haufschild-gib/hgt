import GaloisForLFunctions.RHTower.Suzuki.SuzukiFinitePoleResidueTransport
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelOneSidedSupport

/-!
# Residue-only wrong-support output for Suzuki's finite-pole quotient

On Suzuki's fixed Euler line, the tilted Hankel convolution has integrable Fourier transform
without meromorphic innerness: boundedness of the exact Euler-line quotient and all-order decay of
the Deninger--Meyer transform suffice. Fourier inversion therefore identifies the high-line contour
integral with Suzuki's causal physical kernel throughout the finite-pole range. For the reflection
of a positive-half-line input and a negative-half-line output, that causal term vanishes. Combining
this fact with finite-pole contour transport leaves exactly the complete Laurent-residue sum.
-/

namespace RHTower

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

noncomputable section

/-- At the fixed Euler line, the Fourier transform of Suzuki's tilted Hankel convolution is
integrable without meromorphic innerness. -/
theorem integrable_fourier_suzukiTiltedHankelConvolution_horizontal_one
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget) :
    Integrable (FourierTransform.fourier
      (suzukiTiltedHankelConvolution omega 1 g)) := by
  have hline :=
    (integrable_suzukiCanonicalHankelContourIntegrand_horizontal_one
      homega0 homegaHalf g 0).comp_mul_left'
      (show -2 * Real.pi ≠ 0 by exact mul_ne_zero (by norm_num) Real.pi_ne_zero)
  apply hline.congr
  filter_upwards with xi
  rw [fourier_suzukiTiltedHankelConvolution homega0 (by linarith)]
  rw [suzukiCanonicalHankelContourIntegrand]
  have hMarg : -Complex.I *
      (((-2 * Real.pi * xi : ℝ) : ℂ) + Complex.I) =
        (1 : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
  rw [hMarg]
  simp

/-- Suzuki's fixed Euler-line inversion is unconditional in the finite-pole range; innerness was
used in the older global-unitary theorem only to provide the integrability now proved above. -/
theorem integral_suzukiCanonicalHankelContourIntegrand_horizontal_one_eq_literalLogHankel
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) (r : ℝ) :
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + Complex.I)) =
      (2 * Real.pi : ℂ) * suzukiLiteralLogHankel omega g r := by
  have hconv := integrable_suzukiTiltedHankelConvolution
    (c := 1) homega0 (by linarith) g
  have hfourier :=
    integrable_fourier_suzukiTiltedHankelConvolution_horizontal_one
      homega0 homegaHalf g
  have hinversion := congrFun
    ((continuous_suzukiTiltedHankelConvolution
      (c := 1) homega0 (by linarith) g hg).fourierInv_fourier_eq
      hconv hfourier) r
  rw [Real.fourierInv_eq'] at hinversion
  have hscaled :
      (∫ xi : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          (((-2 * Real.pi * xi : ℝ) : ℂ) + Complex.I)) =
        (Real.exp r : ℂ) * suzukiTiltedHankelConvolution omega 1 g r := by
    rw [← hinversion, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with xi
    rw [fourier_suzukiTiltedHankelConvolution homega0 (by linarith)]
    simp only [smul_eq_mul]
    rw [suzukiCanonicalHankelContourIntegrand]
    have hMarg : -Complex.I *
        (((-2 * Real.pi * xi : ℝ) : ℂ) + Complex.I) =
          (1 : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
    have hexponent :
        -Complex.I *
            (((-2 * Real.pi * xi : ℝ) : ℂ) + Complex.I) * (r : ℂ) =
          (r : ℂ) + (((2 * Real.pi * xi * r : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
    rw [hexponent, hMarg, Complex.exp_add, Complex.ofReal_exp]
    simp only [Real.inner_apply]
    simp only [ofReal_one, one_mul]
    rw [show 2 * Real.pi * xi * r = 2 * Real.pi * (xi * r) by ring]
    ring
  have hdilation := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => suzukiCanonicalHankelContourIntegrand omega g r
      ((u : ℂ) + Complex.I)) (-2 * Real.pi)
  have habs : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + Complex.I)) =
      (2 * Real.pi : ℂ) *
        ∫ xi : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          (((-2 * Real.pi * xi : ℝ) : ℂ) + Complex.I) := by
            rw [hdilation, habs, Complex.real_smul]
            push_cast
            field_simp [Real.pi_ne_zero]
    _ = (2 * Real.pi : ℂ) *
        ((Real.exp r : ℂ) * suzukiTiltedHankelConvolution omega 1 g r) := by
      rw [hscaled]
    _ = (2 * Real.pi : ℂ) * suzukiLiteralLogHankel omega g r := by
      rw [suzukiLiteralLogHankel_eq_exp_mul_tiltedConvolution (c := 1)]
      simp

/-- The Euler line is causal: it contributes nothing on the negative output half-line when the
Hankel source is the reflection of a positive-half-line input. -/
theorem integral_suzukiCanonicalHankelContourIntegrand_horizontal_one_eq_zero_of_negative_support
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ))
    (hsupport : ∀ s : ℝ, 0 ≤ s → (g : ℝ → ℂ) s = 0)
    {r : ℝ} (hr : r < 0) :
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + Complex.I)) = 0 := by
  rw [integral_suzukiCanonicalHankelContourIntegrand_horizontal_one_eq_literalLogHankel
    homega0 homegaHalf g hg r]
  rw [suzukiLiteralLogHankel_eq_zero_of_lt_neg_support g hsupport (by simpa using hr)]
  ring

/-- Complete residue-only transport on the actual wrong-support half-line. -/
theorem horizontalIntegral_normalized_eq_I_mul_sum_laurentCoeff_suzukiCanonical_of_finite
    {omega : ℝ} (homega0 : 0 < omega) (homegaHalf : omega < 1 / 2)
    (P : Finset ℂ) (hP : SuzukiCanonicalFiniteUpperPoleDivisor omega P)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ))
    (hsupport : ∀ s : ℝ, 0 ≤ s → (g : ℝ → ℂ) s = 0)
    {r : ℝ} (hr : r < 0) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ x : ℝ, suzukiCanonicalHankelContourIntegrand omega g r (x : ℂ)) =
      Complex.I * ∑ p ∈ P,
        GaloisForLFunctions.HTGeometry.laurentCoeff
          (suzukiCanonicalHankelContourIntegrand omega g r) p (-1) := by
  have htransport :=
    horizontalIntegral_normalized_sub_eq_I_mul_sum_laurentCoeff_suzukiCanonical_of_finite
      homega0 homegaHalf P hP g r
  have htop :=
    integral_suzukiCanonicalHankelContourIntegrand_horizontal_one_eq_zero_of_negative_support
      homega0 homegaHalf g hg hsupport hr
  rw [htop] at htransport
  simpa using htransport

end

end RHTower
