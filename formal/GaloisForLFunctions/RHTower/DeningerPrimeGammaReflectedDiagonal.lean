import GaloisForLFunctions.RHTower.DeningerPrimeGammaPacketCohomology
import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Reflected-diagonal comparison for prime--Gamma packet cohomology

The off-diagonal source kernel is already the divisor Cauchy polarization.  This file proves the
missing diagonal value.  Around every lower Euler parameter, the centered Xi divisor remains a
uniform positive distance away because all divisor points lie in `|Im z| < 1/2`.  The derivative
series is therefore locally dominated by four times the square-summable Cauchy evaluation.

Termwise differentiation gives

`R'(z) = -∑_q (xiSpectralPoint q - z)⁻²`.

Consequently the removable source value `-R'(z)` is exactly the squared-Cauchy divisor
polarization.  No positivity or RH is used.
-/

open Complex Metric

namespace RHTower

noncomputable section

private def deningerPrimeGammaDifferentiationRadius
    (z : DeningerPrimeGammaLowerPoint) : ℝ :=
  (-(1 / 2 : ℝ) - (z : ℂ).im) / 2

private theorem deningerPrimeGammaDifferentiationRadius_pos
    (z : DeningerPrimeGammaLowerPoint) :
    0 < deningerPrimeGammaDifferentiationRadius z := by
  have hz := z.property
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_re, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_apply] at hz
  norm_num at hz
  unfold deningerPrimeGammaDifferentiationRadius
  linarith

private theorem two_mul_deningerPrimeGammaDifferentiationRadius
    (z : DeningerPrimeGammaLowerPoint) :
    2 * deningerPrimeGammaDifferentiationRadius z =
      -(1 / 2 : ℝ) - (z : ℂ).im := by
  unfold deningerPrimeGammaDifferentiationRadius
  ring

private theorem two_mul_deningerPrimeGammaDifferentiationRadius_lt_norm_sub
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) :
    2 * deningerPrimeGammaDifferentiationRadius z <
      ‖xiSpectralPoint q - (z : ℂ)‖ := by
  have hq := (xiSpectralPoint_im_mem_openHalf q).1
  have him :
      (xiSpectralPoint q).im - (z : ℂ).im ≤
        |(xiSpectralPoint q - (z : ℂ)).im| := by
    rw [Complex.sub_im]
    exact le_abs_self _
  have hnorm := Complex.abs_im_le_norm (xiSpectralPoint q - (z : ℂ))
  rw [two_mul_deningerPrimeGammaDifferentiationRadius]
  calc
    -(1 / 2 : ℝ) - (z : ℂ).im <
        (xiSpectralPoint q).im - (z : ℂ).im := by linarith
    _ ≤ |(xiSpectralPoint q - (z : ℂ)).im| := him
    _ ≤ ‖xiSpectralPoint q - (z : ℂ)‖ := hnorm

private theorem half_norm_sub_lt_norm_sub_of_mem_differentiationBall
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) {u : ℂ}
    (hu : u ∈ Metric.ball (z : ℂ)
      (deningerPrimeGammaDifferentiationRadius z)) :
    ‖xiSpectralPoint q - (z : ℂ)‖ / 2 <
      ‖xiSpectralPoint q - u‖ := by
  have hur :
      ‖u - (z : ℂ)‖ < deningerPrimeGammaDifferentiationRadius z := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have htri :
      ‖xiSpectralPoint q - (z : ℂ)‖ ≤
        ‖xiSpectralPoint q - u‖ + ‖u - (z : ℂ)‖ := by
    calc
      ‖xiSpectralPoint q - (z : ℂ)‖ =
          ‖(xiSpectralPoint q - u) + (u - (z : ℂ))‖ := by ring_nf
      _ ≤ ‖xiSpectralPoint q - u‖ + ‖u - (z : ℂ)‖ := norm_add_le _ _
  have hsep :=
    two_mul_deningerPrimeGammaDifferentiationRadius_lt_norm_sub z q
  linarith

private theorem hasDerivAt_xiRelativeResolventTerm
    (q : XiZeroCopy) {u : ℂ} (hqu : xiSpectralPoint q ≠ u) :
    HasDerivAt (fun v => xiRelativeResolventTerm v q)
      (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u := by
  change HasDerivAt
    (fun v => (xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - v)⁻¹)
    (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u
  have hsub : xiSpectralPoint q - u ≠ 0 := sub_ne_zero.mpr hqu
  convert (hasDerivAt_const (x := u) (c := (xiSpectralPoint q)⁻¹)).sub
    (((hasDerivAt_const (x := u) (c := xiSpectralPoint q)).sub
      (hasDerivAt_id (𝕜 := ℂ) (x := u))).inv hsub) using 1 <;> simp

private theorem norm_xiRelativeResolventTerm_deriv_le
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) {u : ℂ}
    (hu : u ∈ Metric.ball (z : ℂ)
      (deningerPrimeGammaDifferentiationRadius z)) :
    ‖-((xiSpectralPoint q - u)⁻¹ ^ 2)‖ ≤
      4 * ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)‖ ^ 2 := by
  have hhalf :=
    (half_norm_sub_lt_norm_sub_of_mem_differentiationBall z q hu).le
  have haz : 0 < ‖xiSpectralPoint q - (z : ℂ)‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
      (XiC_ne_zero_of_one_lt_centered_re z.property)
        ((XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ)).mpr ⟨q, h⟩))
  have hau : 0 < ‖xiSpectralPoint q - u‖ :=
    lt_of_lt_of_le (half_pos haz) hhalf
  have hinv :
      ‖xiSpectralPoint q - u‖⁻¹ ≤
        2 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ := by
    have h := one_div_le_one_div_of_le (half_pos haz) hhalf
    rw [one_div, one_div, inv_div] at h
    simpa [mul_comm] using h
  rw [norm_neg, norm_pow, norm_inv, xiWeilCauchyTest, norm_inv]
  calc
    ‖xiSpectralPoint q - u‖⁻¹ ^ 2 ≤
        (2 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹) ^ 2 := by
      gcongr
    _ = 4 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ ^ 2 := by ring

/-- The relative-resolvent trace is locally termwise differentiable below the Xi strip. -/
theorem hasDerivAt_xiRelativeResolventTrace_of_eulerPoint
    (z : DeningerPrimeGammaLowerPoint) :
    HasDerivAt xiRelativeResolventTrace
      (∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2))
      (z : ℂ) := by
  let r := deningerPrimeGammaDifferentiationRadius z
  let majorant : XiZeroCopy → ℝ := fun q =>
    4 * ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)‖ ^ 2
  have hr : 0 < r := deningerPrimeGammaDifferentiationRadius_pos z
  have hmajorant : Summable majorant :=
    (XiWeilSquareSummable_cauchy (z : ℂ)).mul_left 4
  have hbase :
      Summable (fun q : XiZeroCopy => xiRelativeResolventTerm (z : ℂ) q) :=
    summable_xiRelativeResolventTerm
      (XiC_ne_zero_of_one_lt_centered_re z.property)
  have hderiv :
      ∀ q : XiZeroCopy, ∀ u ∈ Metric.ball (z : ℂ) r,
        HasDerivAt (fun v => xiRelativeResolventTerm v q)
          (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u := by
    intro q u hu
    apply hasDerivAt_xiRelativeResolventTerm
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp
      (ne_of_gt (lt_of_lt_of_le
        (half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
          (XiC_ne_zero_of_one_lt_centered_re z.property)
            ((XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ)).mpr ⟨q, h⟩))))
        (half_norm_sub_lt_norm_sub_of_mem_differentiationBall z q hu).le)))
  have hbound :
      ∀ q : XiZeroCopy, ∀ u ∈ Metric.ball (z : ℂ) r,
        ‖-((xiSpectralPoint q - u)⁻¹ ^ 2)‖ ≤ majorant q := by
    intro q u hu
    exact norm_xiRelativeResolventTerm_deriv_le z q hu
  change HasDerivAt
    (fun u => ∑' q : XiZeroCopy, xiRelativeResolventTerm u q)
    (∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2))
    (z : ℂ)
  exact hasDerivAt_tsum_of_isPreconnected hmajorant Metric.isOpen_ball
    (convex_ball (z : ℂ) r).isPreconnected hderiv hbound
    (Metric.mem_ball_self hr) hbase (Metric.mem_ball_self hr)

/--
The removable reflected-diagonal prime--Gamma kernel equals the divisor-side squared-Cauchy Weil
polarization.  This closes the atomic source/target comparison at every pair of Euler points.
-/
theorem deningerPrimeGammaSourceKernel_eq_xiWeilPolarization_reflectedDiagonal
    (z : DeningerPrimeGammaLowerPoint) :
    deningerPrimeGammaSourceKernel z (deningerPrimeGammaPointConjEquiv z) =
      xiWeilPolarization
        (xiWeilCauchyTest (z : ℂ))
        (xiWeilCauchyTest
          (deningerPrimeGammaPointConjEquiv z : ℂ)) := by
  rw [deningerPrimeGammaSourceKernel_reflectedDiagonal,
    deriv_primeArchSourceRelativeTrace_eq_deriv_xiRelativeResolventTrace,
    (hasDerivAt_xiRelativeResolventTrace_of_eulerPoint z).deriv]
  rw [xiWeilPolarization]
  calc
    -(∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2)) =
        ∑' q : XiZeroCopy, (xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2 := by
      rw [← tsum_neg]
      simp
    _ = ∑' q : XiZeroCopy,
        xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) *
          xiWeilSharp
            (xiWeilCauchyTest
              (deningerPrimeGammaPointConjEquiv z : ℂ))
            (xiSpectralPoint q) := by
      apply tsum_congr
      intro q
      rw [xiWeilSharp_cauchy]
      simp only [deningerPrimeGammaPointConjEquiv, Equiv.coe_fn_mk,
        starRingEnd_self_apply, xiWeilCauchyTest]
      ring

end

end RHTower
