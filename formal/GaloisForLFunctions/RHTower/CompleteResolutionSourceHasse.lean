import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.CompleteResolutionSourceEmbeddingReflectionLaw

/-!
# Finite-shell Hasse principle for complete-resolution sources

The complete source vector embeds the open spectral right half-plane in a fixed `ℓ¹` space.  Its
individual shell coefficients therefore form local observations which jointly reconstruct the
spectral point; every unequal pair differs at one finite shell.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite shell coefficients form a Hasse family for the spectral right half-plane. -/
def completeResolutionSourceHasseFamily (K : ℕ) :
    HasseFamily CompleteResolutionRightHalfPlane ℕ where
  Local _ := ℂ
  profile s n := completeResolutionSourceEmbedding K s n
  profile_injective := by
    intro s t h
    apply completeResolutionSourceEmbedding_injective K
    apply lp.ext
    funext n
    exact congrFun h n

/-- Spectral points agree exactly when all complete-resolution shell coefficients agree. -/
theorem completeResolutionSource_congr_hasse_iff
    (K : ℕ) (s t : CompleteResolutionRightHalfPlane) :
    (∀ n, completeResolutionSourceEmbedding K s n =
      completeResolutionSourceEmbedding K t n) ↔ s = t :=
  (completeResolutionSourceHasseFamily K).pointwise_eq_iff s t

/-- Unequal spectral points differ in one finite shell coefficient. -/
theorem completeResolutionSource_ne_iff_exists_shell_ne
    (K : ℕ) (s t : CompleteResolutionRightHalfPlane) :
    s ≠ t ↔ ∃ n, completeResolutionSourceEmbedding K s n ≠
      completeResolutionSourceEmbedding K t n :=
  (completeResolutionSourceHasseFamily K).ne_iff_exists_local_ne s t

end

end RHTower
