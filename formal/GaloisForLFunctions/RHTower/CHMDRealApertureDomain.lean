import GaloisForLFunctions.RHTower.CHMDFixedApertureQuotientLanding
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLimitingLogMixedReality

/-!
# The real restricted Weil domain in the arithmetic source graph

The closure of the real smooth aperture core is exactly the part of the
complete restricted Weil domain with a real physical representative.
Orthogonal projection onto that closure is physical real-part extraction.
This identifies the domain of the completed inverse-Doob lift intrinsically.
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace
open GaloisForLFunctions.RHTower

set_option autoImplicit false
noncomputable section
namespace RHTower
open CHMDDoobGraph CHMDPolar

private theorem aperture_core_physical_inner_im (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
  change (inner ℂ (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u))
    (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0
  rw [L2.inner_def]
  have he : (∫ x, inner ℂ
      (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a u) x)
      (ccmArchimedeanFormEmbedding a (suzukiRestrictedWeilCoreCCMFormVector a v) x)) =
      ((∫ x, u x * v x : ℝ) : ℂ) := by
    calc
      _ = ∫ x, ((u x * v x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u,
          ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a v]
          with x hu hv
        rw [hu, hv]
        simp [RCLike.inner_apply, mul_comm]
      _ = _ := integral_ofReal
  rw [he, Complex.ofReal_im]

private theorem aperture_core_prime_inner_im (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ
      (ccmFinitePrimeOperator a
        (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u)))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
  classical
  unfold ccmFinitePrimeOperator
  generalize Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn, ContinuousLinearMap.add_apply, inner_add_left,
        Complex.add_im, ih, add_zero, ContinuousLinearMap.smul_apply, inner_smul_left]
      simp only [Complex.conj_ofReal, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero,
        inner_ccmPrimeTransportOperator_realCore_mixed_im_eq_zero, mul_zero]

/-- The archimedean form inner product is real on real smooth sources.
The finite prime, polar and scalar terms are all real separately. -/
theorem aperture_core_inner_im_eq_zero (a : SuzukiPositiveAperture)
    (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ (suzukiRestrictedWeilCoreCCMFormVector a u)
      (suzukiRestrictedWeilCoreCCMFormVector a v)).im = 0 := by
  have hpolar : (inner ℂ
      (ccmPolarOperator a
        (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a u)))
      (ccmArchimedeanFormToAperture a (suzukiRestrictedWeilCoreCCMFormVector a v))).im = 0 := by
    rw [inner_ccmPolarOperator_mixed]
    simp_rw [inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal]
    simp
  have h := ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u v
  unfold ccmRestrictedWeilForm ccmRestrictedWeilBoundedRemainder at h
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply_eq_self,
    inner_sub_left, inner_add_left, inner_smul_left,
    star_ccmArchimedeanRemainderScalar] at h
  simpa only [Complex.add_im, Complex.sub_im, ccmArchimedeanRemainderScalar,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    aperture_core_physical_inner_im, aperture_core_prime_inner_im, hpolar,
    mul_zero, add_zero, sub_zero] using h

end RHTower
