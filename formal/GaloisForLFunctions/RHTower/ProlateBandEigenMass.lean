import GaloisForLFunctions.RHTower.BandTransformEnergy
import GaloisForLFunctions.RHTower.SlepianKernelScaledFubini
import GaloisForLFunctions.RHTower.ProlateRadialNormalization

/-!
# Exact mass identities for global prolate band eigenfunctions

`BandTransformEnergy` computes the exterior mass of the canonical `eigenExtension` of an
`L²[-1,1]` band eigenvector.  Joint prolate constructions instead produce a continuous function on
the whole line satisfying the pointwise band equation.  This module closes that representation gap:
the pointwise eigenfunction is exactly the extension of its own band class, so its exterior mass is
the spectral leakage ratio `(1 - ν) / ν` times its interior mass.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set

open _root_.RHTower

/-- The pointwise Slepian band transform commutes with real scalar multiplication. -/
theorem bandTransform_const_mul (c r : ℝ) (Φ : ℝ → ℝ) (x : ℝ) :
    bandTransform c (fun y => r * Φ y) x = r * bandTransform c Φ x := by
  rw [bandTransform, bandTransform, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun y _ => ?_
  ring

/-- Endpoint normalization preserves every pointwise band eigen-equation. -/
theorem bandTransform_endpointNormalize_eigen
    {c ν : ℝ} {Φ : ℝ → ℝ}
    (heig : ∀ x : ℝ, bandTransform c Φ x = ν * Φ x) :
  ∀ x : ℝ, bandTransform c (prolateEndpointNormalize Φ) x =
      ν * prolateEndpointNormalize Φ x := by
  intro x
  have hfun : prolateEndpointNormalize Φ = fun y => (Φ 1)⁻¹ * Φ y := by
    funext y
    simp only [prolateEndpointNormalize, div_eq_mul_inv]
    ring
  rw [hfun, bandTransform_const_mul, heig]
  ring

/-- A continuous pointwise band eigenfunction gives an eigenvector of the `L²[-1,1]` band
operator. -/
theorem bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
    {c ν : ℝ} {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heig : ∀ x : ℝ, bandTransform c Φ x = ν * Φ x) :
    bandOperatorL2 c (bandClass Φ hΦ) = ν • bandClass Φ hΦ := by
  have hmul : Continuous (fun x : ℝ => ν * Φ x) := continuous_const.mul hΦ
  have hfun : bandTransform c Φ = fun x : ℝ => ν * Φ x := funext heig
  rw [bandOperatorL2_bandClass,
    bandClass_congr (continuous_bandTransform c hΦ) hmul hfun,
    bandClass_smul hΦ ν hmul]

/-- The whole-line energy of a continuous global band eigenfunction is its aperture energy divided
by the band eigenvalue. -/
theorem integral_sq_global_band_eigen
    {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heig : ∀ x : ℝ, bandTransform c Φ x = ν * Φ x) :
    (∫ x : ℝ, Φ x ^ 2) = ‖bandClass Φ hΦ‖ ^ 2 / ν := by
  have hclass := bandOperatorL2_bandClass_eq_smul_of_global_band_eigen hΦ heig
  have hmass := integral_sq_eigenExtension hc hν hclass
  have hext := _root_.RHTower.eigenExtension_bandClass_eq_self_of_bandEigen hν hΦ heig
  simpa only [hext] using hmass

/-- The exterior energy of a continuous global band eigenfunction is exactly its aperture energy
times the leakage ratio `(1 - ν) / ν`. -/
theorem integral_outside_sq_global_band_eigen
    {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heig : ∀ x : ℝ, bandTransform c Φ x = ν * Φ x) :
    (∫ x in (Icc (-1 : ℝ) 1)ᶜ, Φ x ^ 2) =
      ‖bandClass Φ hΦ‖ ^ 2 * (1 - ν) / ν := by
  have hclass := bandOperatorL2_bandClass_eq_smul_of_global_band_eigen hΦ heig
  have hmass := integral_outside_sq_eigenExtension hc hν hclass
  have hext := _root_.RHTower.eigenExtension_bandClass_eq_self_of_bandEigen hν hΦ heig
  simpa only [hext] using hmass

/-- Integral form of the exact exterior/interior mass identity. -/
theorem integral_outside_sq_global_band_eigen_eq_integral_mul_ratio
    {c ν : ℝ} (hc : 0 < c) (hν : ν ≠ 0) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (heig : ∀ x : ℝ, bandTransform c Φ x = ν * Φ x) :
    (∫ x in (Icc (-1 : ℝ) 1)ᶜ, Φ x ^ 2) =
      (∫ x in (-1 : ℝ)..1, Φ x ^ 2) * (1 - ν) / ν := by
  rw [integral_outside_sq_global_band_eigen hc hν hΦ heig,
    norm_sq_bandClass]

end GaloisForLFunctions.RHTower

end
