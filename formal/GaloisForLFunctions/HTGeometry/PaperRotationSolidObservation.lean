import GaloisForLFunctions.HTGeometry.PaperRotationCalkinFaithfulness
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Uniform masked observations of returning rotation conjugates

Every compact correction vanishes uniformly on all coordinate masks of a
fixed history along the actual return times, although its norm is preserved.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter Topology

theorem paperRotationCompact_uniform_solidHull (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (x : PaperRotationHilbert) :
    TendstoUniformlyOn (fun N y =>
      paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1 y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ ‖K.1‖ (norm_nonneg _)
    (fun N => (paperRotationConjugation_norm (paperRotationReturnTime t N : ℤ) K.1).le)
    (paperRotation_compact_conjugation_tendsto t K) x

theorem paperRotationCompact_uniform_masks (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (x : PaperRotationHilbert) :
    TendstoUniformly (fun N m =>
      paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1 (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ ‖K.1‖ (norm_nonneg _)
    (fun N => (paperRotationConjugation_norm (paperRotationReturnTime t N : ℤ) K.1).le)
    (paperRotation_compact_conjugation_tendsto t K) x

theorem paperRotationCompact_solidObservation_tendsto (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (x : PaperRotationHilbert) :
    Tendsto (fun N => lpSolidObservation
      (paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ ‖K.1‖ (norm_nonneg _)
    (fun N => (paperRotationConjugation_norm (paperRotationReturnTime t N : ℤ) K.1).le)
    (paperRotation_compact_conjugation_tendsto t K) x

theorem paperRotationCompact_moving_mask_tendsto (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (x : PaperRotationHilbert)
    (m : ℕ → LpCoordinateMask ℤ) :
    Tendsto (fun N => paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1
      (lpMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ ‖K.1‖ (norm_nonneg _)
    (fun N => (paperRotationConjugation_norm (paperRotationReturnTime t N : ℤ) K.1).le)
    (paperRotation_compact_conjugation_tendsto t K) x m

theorem paperRotationCompact_observation_attained (t : ℝ)
    (K : compactOperatorStarAlgebra PaperRotationHilbert) (N : ℕ) (x : PaperRotationHilbert) :
    ∃ m : LpCoordinateMask ℤ,
      ‖paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1 (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperRotationConjugation (paperRotationReturnTime t N : ℤ) K.1) x :=
  lpSolidObservation_attained _ x

end
end GaloisForLFunctions.HTGeometry
