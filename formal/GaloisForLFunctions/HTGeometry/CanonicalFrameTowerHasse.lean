import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.CompleteFrameTowerTopology
import GaloisForLFunctions.HTGeometry.InfiniteSupportBoundaryCarrier

/-!
# Hasse principles for canonical frame towers

Canonical positive-diagonal inverse-Cholesky factors provide nonlinear finite-dimensional local
coordinates for probability laws.  Their complete towers separate positive-Gram laws,
infinite-support laws, and infinite-support Nevanlinna boundary parameter laws.  Every unequal pair
is therefore detected at one finite frame level.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Canonical finite frames form a Hasse family on the positive Cayley-Gram domain. -/
noncomputable def completeCanonicalFrameHasseFamily :
    HasseFamily PositiveCayleyGramProbability ℕ where
  Local N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  profile := completeCanonicalFrameTower
  profile_injective := injective_completeCanonicalFrameTower

/-- Positive-Gram probability laws agree exactly when all canonical frame levels agree. -/
theorem positiveCayleyGramProbability_congr_frame_hasse_iff
    (mu nu : PositiveCayleyGramProbability) :
    (∀ N, completeCanonicalFrameTower mu N = completeCanonicalFrameTower nu N) ↔ mu = nu :=
  completeCanonicalFrameHasseFamily.pointwise_eq_iff mu nu

/-- Unequal positive-Gram probability laws differ at one finite canonical frame level. -/
theorem positiveCayleyGramProbability_ne_iff_exists_frame_ne
    (mu nu : PositiveCayleyGramProbability) :
    mu ≠ nu ↔ ∃ N, completeCanonicalFrameTower mu N ≠ completeCanonicalFrameTower nu N :=
  completeCanonicalFrameHasseFamily.ne_iff_exists_local_ne mu nu

/-- Canonical finite frames form a Hasse family on infinite-support probability laws, with
finite-level positivity derived internally from support. -/
noncomputable def completeInfiniteSupportCanonicalFrameHasseFamily :
    HasseFamily InfiniteSupportProbability ℕ where
  Local N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  profile := completeInfiniteSupportCanonicalFrameTower
  profile_injective := injective_completeInfiniteSupportCanonicalFrameTower

/-- Infinite-support probability laws agree exactly when all canonical frame levels agree. -/
theorem infiniteSupportProbability_congr_frame_hasse_iff
    (mu nu : InfiniteSupportProbability) :
    (∀ N, completeInfiniteSupportCanonicalFrameTower mu N =
      completeInfiniteSupportCanonicalFrameTower nu N) ↔ mu = nu :=
  completeInfiniteSupportCanonicalFrameHasseFamily.pointwise_eq_iff mu nu

/-- Unequal infinite-support probability laws differ at one finite canonical frame level. -/
theorem infiniteSupportProbability_ne_iff_exists_frame_ne
    (mu nu : InfiniteSupportProbability) :
    mu ≠ nu ↔ ∃ N, completeInfiniteSupportCanonicalFrameTower mu N ≠
      completeInfiniteSupportCanonicalFrameTower nu N :=
  completeInfiniteSupportCanonicalFrameHasseFamily.ne_iff_exists_local_ne mu nu

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Boundary canonical frames form a Hasse family for infinite-support projective parameter
laws. -/
noncomputable def completeBoundaryCanonicalFrameHasseFamily :
    HasseFamily InfiniteSupportProjectiveProbability ℕ where
  Local N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  profile := F.completeBoundaryCanonicalFrameTower
  profile_injective := F.injective_completeBoundaryCanonicalFrameTower

/-- Infinite-support projective parameter laws agree exactly when their boundary carrier frames
agree at every finite level. -/
theorem infiniteSupportProjectiveProbability_congr_boundaryFrame_hasse_iff
    (eta theta : InfiniteSupportProjectiveProbability) :
    (∀ N, F.completeBoundaryCanonicalFrameTower eta N =
      F.completeBoundaryCanonicalFrameTower theta N) ↔ eta = theta :=
  F.completeBoundaryCanonicalFrameHasseFamily.pointwise_eq_iff eta theta

/-- Unequal infinite-support projective laws differ at one finite boundary frame level. -/
theorem infiniteSupportProjectiveProbability_ne_iff_exists_boundaryFrame_ne
    (eta theta : InfiniteSupportProjectiveProbability) :
    eta ≠ theta ↔ ∃ N, F.completeBoundaryCanonicalFrameTower eta N ≠
      F.completeBoundaryCanonicalFrameTower theta N :=
  F.completeBoundaryCanonicalFrameHasseFamily.ne_iff_exists_local_ne eta theta

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
