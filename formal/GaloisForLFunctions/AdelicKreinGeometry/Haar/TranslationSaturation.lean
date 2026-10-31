import GaloisForLFunctions.HeckeKreinToeplitz.Index.PeriodicSaturation
import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationMovingPositivity
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PeriodicTranslations

/-!
# Identity-value saturation in periodic affine kernels

Finite negative index makes every rational translation moving space positive.
A translation having the identity coefficient therefore becomes a two-sided period.
-/

open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A saturated translation becomes a right period of an integer-invariant finite-index kernel. -/
theorem translation_saturation_right_invariant {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ)
    (hsat : k (translation b) = k 1) (g : AffineGroupQ) :
    k (g * translation b) = k g :=
  periodic_saturation_right_invariant hk (translation b)
    (kernel_translation_locally_periodic hp b)
    (translation_moving_subspace_nonnegative hk hi hp b) hsat g

/-- The same saturated translation is also a left period. -/
theorem translation_saturation_left_invariant {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ)
    (hsat : k (translation b) = k 1) (g : AffineGroupQ) :
    k (translation b * g) = k g :=
  isHermKernel_left_invariant_of_right hk (translation b)
    (translation_saturation_right_invariant hk hi hp b hsat) g

#print axioms translation_saturation_right_invariant
#print axioms translation_saturation_left_invariant
end GaloisForLFunctions.AdelicKreinGeometry
