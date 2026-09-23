import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelKernelBridge
import GaloisForLFunctions.HTGeometry.CausalFourierBridge
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Suzuki's literal logarithmic Hankel kernel by Fourier inversion

This file completes the classical integral part of Suzuki (2012), Lemma 4.1.  For a compactly
supported smooth logarithmic source `g`, the exact arithmetic kernel is tilted into `L¹`, paired
with a reflected tilted source, and treated as an ordinary convolution.  Its Fourier transform is
the exact product of Suzuki's shifted-Xi quotient and the logarithmic Mellin transform.  Fourier
inversion and the source-faithful contour shift then prove

`∫_ℝ Θ_ω(u+ic) M_g(-i(u+ic)) exp(-i(u+ic)r) du
  = 2π ∫_ℝ exp((r+s)/2) h_ω(exp(r+s)) g(s) ds`.

No transform identity is assumed, no proxy kernel is introduced, and no numerical computation is
used.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform Convolution

namespace RHTower

noncomputable section

/-- Integrability form of `x = exp(t)`, kept local to the Suzuki dependency graph. -/
theorem suzuki_integrableOn_Ioi_iff_integrable_exp_smul (f : ℝ → ℂ) :
    IntegrableOn f (Ioi (0 : ℝ)) ↔
      Integrable (fun t : ℝ => Real.exp t • f (Real.exp t)) := by
  rw [← Real.range_exp, ← Set.image_univ,
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn,
    integrableOn_univ]
  simp only [abs_of_pos (Real.exp_pos _)]

/-- Exponentially tilted logarithmic form of Suzuki's literal arithmetic kernel. -/
def suzukiLogKernelTilt (omega c t : ℝ) : ℂ :=
  (Real.exp ((1 / 2 - c) * t) : ℂ) *
    suzukiSourceHFinite omega (Real.exp t)

theorem integrable_suzukiLogKernelTilt
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c) :
    Integrable (suzukiLogKernelTilt omega c) := by
  have hM := (suzuki2012_proposition_one homega
    (z := (c : ℂ) * Complex.I) (by
      simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero]
      norm_num at hc ⊢
      exact hc)).1
  rw [MellinConvergent] at hM
  have hlog := (suzuki_integrableOn_Ioi_iff_integrable_exp_smul
    (fun x : ℝ => (x : ℂ) ^
      ((1 / 2 + ((c : ℂ) * Complex.I) * Complex.I) - 1) •
        suzukiSourceHFinite omega x)).mp hM
  apply hlog.congr
  filter_upwards with t
  rw [suzukiLogKernelTilt]
  simp only [smul_eq_mul]
  rw [Complex.ofReal_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_nonneg])]
  rw [Complex.real_smul, Complex.ofReal_exp]
  rw [show Complex.exp (t : ℂ) *
      (Complex.exp ((t : ℂ) * (1 / 2 + (c : ℂ) * I * I - 1)) *
        suzukiSourceHFinite omega (Real.exp t)) =
      (Complex.exp (t : ℂ) *
        Complex.exp ((t : ℂ) * (1 / 2 + (c : ℂ) * I * I - 1))) *
          suzukiSourceHFinite omega (Real.exp t) by ring]
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 2
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

/-- Exact logarithmic-coordinate formula for the Mellin transform. -/
theorem mellin_eq_integral_exp_mul_log (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ t : ℝ, Complex.exp (s * (t : ℂ)) * f (Real.exp t) := by
  rw [mellin_eq_fourier, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [neg_neg, show -s.re * -t = s.re * t by ring]
  simp only [smul_eq_mul]
  change Complex.exp (((-2 * Real.pi * -t * (s.im / (2 * Real.pi)) : ℝ) : ℂ) * I) *
      (((Real.exp (s.re * t) : ℝ) : ℂ) * f (Real.exp t)) =
    Complex.exp (s * (t : ℂ)) * f (Real.exp t)
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  have hphase : -2 * Real.pi * -t * (s.im / (2 * Real.pi)) = s.im * t := by
    field_simp
  rw [hphase]
  apply Complex.ext <;> simp

theorem fourier_suzukiLogKernelTilt
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c) (xi : ℝ) :
    FourierTransform.fourier (suzukiLogKernelTilt omega c) xi =
      suzukiCanonicalTheta omega
        (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I) := by
  let z : ℂ := ((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I
  have hz : 1 / 2 + omega < z.im := by
    dsimp only [z]
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_add, mul_one]
    norm_num at hc ⊢
    exact hc
  have hp := suzuki2012_proposition_one homega hz
  rw [← hp.2, mellin_eq_integral_exp_mul_log,
    Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [suzukiLogKernelTilt]
  simp only [smul_eq_mul]
  rw [Complex.ofReal_exp]
  have hexponent :
      (((-2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I) +
          (((1 / 2 - c) * t : ℝ) : ℂ) =
        ((((1 / 2 : ℝ) : ℂ) + z * Complex.I) * (t : ℂ)) := by
    dsimp only [z]
    push_cast
    have hzi :
        ((-2 * (Real.pi : ℂ) * (xi : ℂ) + (c : ℂ) * Complex.I) * Complex.I) =
          (-2 * (Real.pi : ℂ) * (xi : ℂ)) * Complex.I - (c : ℂ) := by
      rw [add_mul, mul_assoc ((c : ℂ)) Complex.I Complex.I, Complex.I_mul_I]
      ring
    rw [hzi]
    ring
  calc
    Complex.exp (((-2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (((1 / 2 - c) * t : ℝ) : ℂ) *
          suzukiSourceHFinite omega (Real.exp t)) =
      (Complex.exp (((-2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((1 / 2 - c) * t : ℝ) : ℂ)) *
          suzukiSourceHFinite omega (Real.exp t) := by ring
    _ = Complex.exp
        ((((-2 * Real.pi * t * xi : ℝ) : ℂ) * Complex.I) +
          (((1 / 2 - c) * t : ℝ) : ℂ)) *
          suzukiSourceHFinite omega (Real.exp t) := by rw [Complex.exp_add]
    _ = Complex.exp
        ((((1 / 2 : ℝ) : ℂ) + z * Complex.I) * (t : ℂ)) *
          suzukiSourceHFinite omega (Real.exp t) := by rw [hexponent]
    _ = Complex.exp ((1 / 2 + z * Complex.I) * (t : ℂ)) *
          suzukiSourceHFinite omega (Real.exp t) := by norm_num

/-- Exponentially tilted compact-smooth source. -/
def suzukiSourceTilt (c : ℝ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) : ℂ :=
  deningerMeyerWeightedLogProfile c g t

/-- Reflection used to express the Hankel sum kernel as an ordinary convolution. -/
def suzukiSourceTiltReflection
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) : ℂ :=
  suzukiSourceTilt c g (-t)

theorem integrable_suzukiSourceTilt
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    Integrable (suzukiSourceTilt c g) :=
  integrable_deningerMeyerWeightedLogProfile g.property c

theorem integrable_suzukiSourceTiltReflection
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    Integrable (suzukiSourceTiltReflection c g) := by
  change Integrable (fun t : ℝ => suzukiSourceTilt c g (-t))
  exact (integrable_suzukiSourceTilt c g).comp_neg

theorem continuous_suzukiSourceTiltReflection
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    Continuous (suzukiSourceTiltReflection c g) := by
  unfold suzukiSourceTiltReflection suzukiSourceTilt deningerMeyerWeightedLogProfile
  exact ((by fun_prop : Continuous fun t : ℝ => (Real.exp (c * -t) : ℂ))).mul
    (g.property.smooth.continuous.comp continuous_neg)

theorem hasCompactSupport_suzukiSourceTiltReflection
    (c : ℝ) (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    HasCompactSupport (suzukiSourceTiltReflection c g) := by
  have htilt : HasCompactSupport (suzukiSourceTilt c g) := by
    change HasCompactSupport
      ((fun t : ℝ => (Real.exp (c * t) : ℂ)) * (g : ℝ → ℂ))
    exact hg.mul_left
  change HasCompactSupport (fun t : ℝ => suzukiSourceTilt c g (-t))
  exact htilt.comp_homeomorph (Homeomorph.neg ℝ)

theorem fourier_suzukiSourceTiltReflection
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (xi : ℝ) :
    FourierTransform.fourier (suzukiSourceTiltReflection c g) xi =
      deningerMeyerStrongLogMellin g
        ((c : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul, deningerMeyerStrongLogMellin,
    ← integral_neg_eq_self]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [suzukiSourceTiltReflection, suzukiSourceTilt, deningerMeyerWeightedLogProfile,
    deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul, neg_neg, smul_eq_mul]
  rw [Complex.ofReal_exp]
  rw [show Complex.exp (((-2 * Real.pi * -t * xi : ℝ) : ℂ) * Complex.I) *
      (Complex.exp ((c * t : ℝ) : ℂ) * (g : ℝ → ℂ) t) =
    (Complex.exp (((-2 * Real.pi * -t * xi : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((c * t : ℝ) : ℂ)) * (g : ℝ → ℂ) t by ring,
    ← Complex.exp_add]
  congr 2
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

def suzukiTiltedHankelConvolution
    (omega c : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) : ℂ :=
  (suzukiLogKernelTilt omega c ⋆[ContinuousLinearMap.mul ℂ ℂ]
    suzukiSourceTiltReflection c g) r

theorem integrable_suzukiTiltedHankelConvolution
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (g : DeningerMeyerStrongLogTarget) :
    Integrable (suzukiTiltedHankelConvolution omega c g) := by
  exact (integrable_suzukiLogKernelTilt homega hc).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_suzukiSourceTiltReflection c g)

theorem continuous_suzukiTiltedHankelConvolution
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) :
    Continuous (suzukiTiltedHankelConvolution omega c g) := by
  exact (hasCompactSupport_suzukiSourceTiltReflection c g hg).continuous_convolution_right
    (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_suzukiLogKernelTilt homega hc).locallyIntegrable
    (continuous_suzukiSourceTiltReflection c g)

theorem fourier_suzukiTiltedHankelConvolution
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (g : DeningerMeyerStrongLogTarget) (xi : ℝ) :
    FourierTransform.fourier (suzukiTiltedHankelConvolution omega c g) xi =
      suzukiCanonicalTheta omega
          (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I) *
        deningerMeyerStrongLogMellin g
          ((c : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) := by
  change FourierTransform.fourier
      (suzukiLogKernelTilt omega c ⋆[ContinuousLinearMap.mul ℂ ℂ]
        suzukiSourceTiltReflection c g) xi = _
  rw [fourier_mul_convolution_eq_of_integrable
      (integrable_suzukiLogKernelTilt homega hc)
      (integrable_suzukiSourceTiltReflection c g),
    fourier_suzukiLogKernelTilt homega hc,
    fourier_suzukiSourceTiltReflection]

theorem integrable_fourier_suzukiTiltedHankelConvolution
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget) :
    Integrable (FourierTransform.fourier
      (suzukiTiltedHankelConvolution omega c g)) := by
  let C : ℝ :=
    (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 c g t) +
      ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 c g t
  have hc0 : 0 ≤ c := by linarith
  have hscale : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hmajorant : Integrable (fun xi : ℝ =>
      C * (1 + (2 * Real.pi * xi) ^ (2 : ℕ))⁻¹) := by
    exact (integrable_inv_one_add_sq.comp_mul_left' hscale).const_mul C
  have hconv := integrable_suzukiTiltedHankelConvolution homega hc g
  have hcontinuous : Continuous (FourierTransform.fourier
      (suzukiTiltedHankelConvolution omega c g)) :=
    VectorFourier.fourierIntegral_continuous continuous_fourierChar
      (by
        simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial]
        fun_prop)
      hconv
  apply Integrable.mono' hmajorant hcontinuous.aestronglyMeasurable
  filter_upwards [] with xi
  rw [fourier_suzukiTiltedHankelConvolution homega hc, norm_mul]
  have htheta : ‖suzukiCanonicalTheta omega
      (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I)‖ ≤ 1 := by
    apply norm_suzukiCanonicalTheta_le_one_of_im_nonneg hinner
    simpa only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_add,
      mul_one, mul_zero, add_zero] using hc0
  have hM := norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
    g hc0 hc0 le_rfl (2 * Real.pi * xi)
  calc
    ‖suzukiCanonicalTheta omega
          (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I)‖ *
        ‖deningerMeyerStrongLogMellin g
          ((c : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I)‖ ≤
      1 * (C * (1 + (2 * Real.pi * xi) ^ (2 : ℕ))⁻¹) := by gcongr
    _ = C * (1 + (2 * Real.pi * xi) ^ (2 : ℕ))⁻¹ := one_mul _

/-- Literal logarithmic form of Suzuki's kernel operator. -/
def suzukiLiteralLogHankel
    (omega : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) : ℂ :=
  ∫ s : ℝ, (Real.exp ((r + s) / 2) : ℂ) *
    suzukiSourceHFinite omega (Real.exp (r + s)) * (g : ℝ → ℂ) s

theorem suzukiLiteralLogHankel_eq_exp_mul_tiltedConvolution
    (omega c : ℝ) (g : DeningerMeyerStrongLogTarget) (r : ℝ) :
    suzukiLiteralLogHankel omega g r =
      (Real.exp (c * r) : ℂ) * suzukiTiltedHankelConvolution omega c g r := by
  rw [suzukiLiteralLogHankel, suzukiTiltedHankelConvolution,
    MeasureTheory.convolution_def]
  change (∫ s : ℝ, (Real.exp ((r + s) / 2) : ℂ) *
      suzukiSourceHFinite omega (Real.exp (r + s)) * (g : ℝ → ℂ) s) =
    (Real.exp (c * r) : ℂ) *
      ∫ t : ℝ, suzukiLogKernelTilt omega c t *
        suzukiSourceTiltReflection c g (r - t)
  have hshift := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => suzukiLogKernelTilt omega c t *
      suzukiSourceTiltReflection c g (r - t)) r
  rw [← hshift, ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [suzukiLogKernelTilt, suzukiSourceTiltReflection, suzukiSourceTilt,
    deningerMeyerWeightedLogProfile]
  have harg : r - (s + r) = -s := by ring
  rw [harg, neg_neg]
  rw [show (Real.exp (c * r) : ℂ) *
      (((Real.exp ((1 / 2 - c) * (s + r)) : ℂ) *
          suzukiSourceHFinite omega (Real.exp (s + r))) *
        ((Real.exp (c * s) : ℂ) * (g : ℝ → ℂ) s)) =
      (((Real.exp (c * r) : ℂ) *
        (Real.exp ((1 / 2 - c) * (s + r)) : ℂ) *
        (Real.exp (c * s) : ℂ)) *
          suzukiSourceHFinite omega (Real.exp (s + r))) *
            (g : ℝ → ℂ) s by ring]
  congr 2
  · norm_cast
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · congr 2 <;> ring

/-- **Suzuki (2012), Lemma 4.1, exact high-line inversion identity.** -/
theorem integral_suzukiCanonicalHankelContourIntegrand_eq_literalLogHankel
    {omega c : ℝ} (homega : 0 < omega) (hc : 1 / 2 + omega < c)
    (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (g : DeningerMeyerStrongLogTarget)
    (hg : HasCompactSupport (g : ℝ → ℂ)) (r : ℝ) :
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + (c : ℂ) * Complex.I)) =
      (2 * Real.pi : ℂ) * suzukiLiteralLogHankel omega g r := by
  have hconv := integrable_suzukiTiltedHankelConvolution homega hc g
  have hfourier :=
    integrable_fourier_suzukiTiltedHankelConvolution homega hc hinner g
  have hinversion := congrFun
    ((continuous_suzukiTiltedHankelConvolution homega hc g hg).fourierInv_fourier_eq
      hconv hfourier) r
  rw [Real.fourierInv_eq'] at hinversion
  have hscaled :
      (∫ xi : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I)) =
        (Real.exp (c * r) : ℂ) * suzukiTiltedHankelConvolution omega c g r := by
    rw [← hinversion, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with xi
    rw [fourier_suzukiTiltedHankelConvolution homega hc]
    simp only [smul_eq_mul]
    rw [suzukiCanonicalHankelContourIntegrand]
    have hMarg : -Complex.I *
        (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I) =
          (c : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
    have hexponent :
        -Complex.I *
            (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I) *
              (r : ℂ) =
          ((c * r : ℝ) : ℂ) +
            (((2 * Real.pi * xi * r : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
    rw [hexponent, hMarg, Complex.exp_add, Complex.ofReal_exp]
    simp only [Real.inner_apply]
    ring
  have hdilation := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => suzukiCanonicalHankelContourIntegrand omega g r
      ((u : ℂ) + (c : ℂ) * Complex.I)) (-2 * Real.pi)
  have habs : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    simp [abs_mul, abs_of_pos Real.pi_pos]
  calc
    (∫ u : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
        ((u : ℂ) + (c : ℂ) * Complex.I)) =
      (2 * Real.pi : ℂ) *
        ∫ xi : ℝ, suzukiCanonicalHankelContourIntegrand omega g r
          (((-2 * Real.pi * xi : ℝ) : ℂ) + (c : ℂ) * Complex.I) := by
            rw [hdilation, habs, Complex.real_smul]
            push_cast
            field_simp [Real.pi_ne_zero]
    _ = (2 * Real.pi : ℂ) *
        ((Real.exp (c * r) : ℂ) *
          suzukiTiltedHankelConvolution omega c g r) := by rw [hscaled]
    _ = (2 * Real.pi : ℂ) * suzukiLiteralLogHankel omega g r := by
      rw [suzukiLiteralLogHankel_eq_exp_mul_tiltedConvolution]

end

end RHTower
