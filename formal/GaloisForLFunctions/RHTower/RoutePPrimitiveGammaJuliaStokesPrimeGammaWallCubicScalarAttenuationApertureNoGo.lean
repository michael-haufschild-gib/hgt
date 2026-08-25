import GaloisForLFunctions.RHTower.XiWardCubicApertureRateChangeDefectLaw

/-!
# Constant scalar attenuation cannot repair the cubic aperture landing

The raw Euler/Gamma--Wold cubic source is far larger than the canonical Xi Malgrange target, so a
viable landing needs strong contraction.  This module rules out the most direct repair: no nonzero
constant scalar, however small, lets an aperture-translation intertwiner change a primitive Burnol
conormal into a strict-right Xi conormal.  The exact positive survivor is the scaled polar--Gamma
boundary work forced by every rate-changing landing.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact boundary work for a scalar-attenuated change of cubic radial character. -/
theorem xiWardCubicApertureCovarianceDefect_scaled_mode_landing_apply_zero :
    ∀ (alpha : ℂ) (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ))
      (z w : ℂ) (c : ℝ),
      T (xiWardCubicRadialGeneralizedMode z) =
          alpha • xiWardCubicRadialGeneralizedMode w →
        xiWardCubicApertureCovarianceDefect T c
            (Complex.exp (-(z * (c : ℂ))))
            (xiWardCubicRadialGeneralizedMode z) 0 =
          alpha * (2 * (c : ℂ) * Complex.exp (-(w * (c : ℂ))) *
            (Complex.exp (-(z * (c : ℂ))) -
              Complex.exp (-(w * (c : ℂ))))) := by
  intro alpha T z w c hland
  rw [xiWardCubicApertureCovarianceDefect,
    xiWardCubicRadialSecondDifference_mode, map_zero]
  simp only [Pi.zero_apply, Pi.sub_apply, zero_sub]
  rw [hland]
  have hsmul :
      xiWardCubicRadialSecondDifference c
          (Complex.exp (-(z * (c : ℂ))))
          (alpha • xiWardCubicRadialGeneralizedMode w) =
        alpha • xiWardCubicRadialSecondDifference c
          (Complex.exp (-(z * (c : ℂ))))
          (xiWardCubicRadialGeneralizedMode w) := by
    ext r
    simp only [xiWardCubicRadialSecondDifference, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsmul]
  change -(alpha * xiWardCubicRadialSecondDifference c
      (Complex.exp (-(z * (c : ℂ))))
      (xiWardCubicRadialGeneralizedMode w) 0) = _
  rw [xiWardCubicRadialSecondDifference_mode_apply_zero_eq]
  ring

/-- **Scalar-attenuation aperture no-go.** No nonzero constant scalar, including an arbitrarily
small contraction, makes a translation-covariant linear map carry a primitive Euler conormal to a
strict-right Xi conormal. -/
theorem not_exists_nonzero_scalar_apertureIntertwiner_primitive_to_strictRight
    (q : XiRightZeroCopy) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ¬ ∃ (alpha : ℂ) (T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ)),
      alpha ≠ 0 ∧
      (∀ c f,
        T (xiWardCubicRadialTranslate c f) =
          xiWardCubicRadialTranslate c (T f)) ∧
      T (xiWardCubicBurnolWindowConormalFeature ·
          (routePPrimitiveBurnolSpectralPoint pe kappa)) =
        alpha • routePXiBaseConormalResidueFeature (q.1.1 : ℂ) := by
  rintro ⟨alpha, T, halpha, hcomm, hland⟩
  apply not_exists_apertureIntertwiner_primitive_to_strictRight q pe kappa
  refine ⟨alpha⁻¹ • T, ?_, ?_⟩
  · intro c f
    ext r
    change alpha⁻¹ * T (xiWardCubicRadialTranslate c f) r =
      alpha⁻¹ * T f (r + c)
    rw [hcomm]
    rfl
  · ext r
    change alpha⁻¹ * T (xiWardCubicBurnolWindowConormalFeature ·
        (routePPrimitiveBurnolSpectralPoint pe kappa)) r =
      routePXiBaseConormalResidueFeature (q.1.1 : ℂ) r
    rw [hland]
    change alpha⁻¹ * (alpha *
      routePXiBaseConormalResidueFeature (q.1.1 : ℂ) r) =
        routePXiBaseConormalResidueFeature (q.1.1 : ℂ) r
    rw [← mul_assoc, inv_mul_cancel₀ halpha, one_mul]

end

end RHTower
