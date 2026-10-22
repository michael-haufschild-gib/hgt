import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaCharacteristicRealization
import GaloisForLFunctions.HTGeometry.SelfAdjointResolventHerglotzEnergy

/-!
# Source-faithful Herglotz energy for Suzuki's actual self-adjoint extension

The generic resolvent identity is instantiated on Suzuki's literal energy space and von Neumann
self-adjoint extension.  It supplies an exact positive graph-energy carrier without replacing the
unbounded source by a finite spectral model.  It does not identify this carrier with Suzuki's
finite characteristic; that comparison remains a separate RH-bearing problem.
-/

open Complex
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Normalized resolvent readout on Suzuki's concrete self-adjoint extension. -/
def suzukiTaActualResolventHerglotzEnergy (a : SuzukiPositiveAperture) (theta : ℝ)
    {z : ℂ} (hz : z.im ≠ 0) (v : SuzukiTaHilbert a) : ℂ :=
  resolventHerglotzEnergy (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz v

/-- Suzuki's literal self-adjoint resolvent has exact positive graph-energy imaginary part. -/
theorem suzukiTaActualResolventHerglotzEnergy_im_eq_graphEnergy
    (a : SuzukiPositiveAperture) (theta : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (v : SuzukiTaHilbert a) :
    (suzukiTaActualResolventHerglotzEnergy a theta hz v).im =
      z.im *
        (‖suzukiTaSelfAdjointExtension a theta
            ⟨resolventLinear (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz v,
              resolventLinear_mem (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz v⟩‖ ^ (2 : ℕ) +
          ‖resolventLinear (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz v‖ ^ (2 : ℕ)) := by
  exact resolventHerglotzEnergy_im_eq_graphEnergy
    (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz v

/-- A nonzero literal Suzuki source has strictly positive resolvent energy in the upper half plane. -/
theorem suzukiTaActualResolventHerglotzEnergy_im_pos
    (a : SuzukiPositiveAperture) (theta : ℝ) {z : ℂ} (hz : 0 < z.im)
    {v : SuzukiTaHilbert a} (hv : v ≠ 0) :
    0 < (suzukiTaActualResolventHerglotzEnergy a theta (ne_of_gt hz) v).im := by
  exact resolventHerglotzEnergy_im_pos
    (suzukiTaSelfAdjointExtension_isSelfAdjoint a theta) hz hv

/-- The closure component in the resolvent boundary quotient is not orthogonal to the literal
Suzuki spectral vector.  Thus graph-energy positivity cannot discard it by a norm split. -/
theorem exists_suzukiTaMinimalClosure_inner_spectralVector_eq_one
    (a : SuzukiPositiveAperture) (z : ℂ) :
    ∃ c : (suzukiTaMinimalDerivative a).closure.domain,
      inner ℂ (suzukiTaSpectralVector a z) (c : SuzukiTaHilbert a) = 1 := by
  let u := suzukiTaSpectralMomentNormalizer a z
  let c0 : (suzukiTaMinimalDerivative a).domain :=
    suzukiTaSmoothCoreEquivRange a u
  let c : (suzukiTaMinimalDerivative a).closure.domain :=
    ⟨(c0 : SuzukiTaHilbert a), (suzukiTaMinimalDerivative a).le_closure.1 c0.property⟩
  refine ⟨c, ?_⟩
  change inner ℂ (suzukiTaSpectralVector a z)
    (suzukiTaSmoothCoreToHilbert a u) = 1
  rw [suzukiTaSpectralVector_inner, suzukiTaSpectralMoment_normalizer]

end RHTower
