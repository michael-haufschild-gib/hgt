import GaloisForLFunctions.RHTower.PaperThetaSchurFiniteStageLimit
import GaloisForLFunctions.HTGeometry.HilbertTruncationNorm
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # All masked histories of the literal theta-stage charge

For every actual Schur family, finite-stage errors disappear uniformly over
each full solid history hull. This conclusion has no RH hypothesis.
-/

namespace RHTower.HedenmalmThetaSource
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

def paperThetaSchurObservationDefect (S : PaperThetaSchurFamily) (N : ℕ) :
    PaperThetaSchurSpace →L[ℂ] PaperThetaSchurSpace :=
  paperThetaSchurModeOperator S - paperThetaSchurFiniteStageOperator S N

theorem paperThetaSchurObservationDefect_norm_le (S : PaperThetaSchurFamily) (N : ℕ) :
    ‖paperThetaSchurObservationDefect S N‖ ≤ ‖paperThetaSchurModeOperator S‖ :=
  norm_sub_hsTruncation_le_norm _ _ _

theorem paperThetaSchurObservationDefect_strong (S : PaperThetaSchurFamily)
    (x : PaperThetaSchurSpace) :
    Tendsto (fun N => paperThetaSchurObservationDefect S N x) atTop (𝓝 0) := by
  simpa only [paperThetaSchurObservationDefect, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperThetaSchurModeOperator S x)).sub
      (paperThetaSchurFiniteStageOperator_strong_tendsto S x)

theorem paperThetaSchurFinite_uniform_solidHull (S : PaperThetaSchurFamily)
    (x : PaperThetaSchurSpace) :
    TendstoUniformlyOn (fun N y => paperThetaSchurObservationDefect S N y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ _ (norm_nonneg _)
    (paperThetaSchurObservationDefect_norm_le S) (paperThetaSchurObservationDefect_strong S) x

theorem paperThetaSchurFinite_uniform_masks (S : PaperThetaSchurFamily)
    (x : PaperThetaSchurSpace) :
    TendstoUniformly (fun N m => paperThetaSchurObservationDefect S N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ _ (norm_nonneg _)
    (paperThetaSchurObservationDefect_norm_le S) (paperThetaSchurObservationDefect_strong S) x

theorem paperThetaSchurFinite_solidObservation_tendsto (S : PaperThetaSchurFamily)
    (x : PaperThetaSchurSpace) :
    Tendsto (fun N => lpSolidObservation (paperThetaSchurObservationDefect S N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ _ (norm_nonneg _)
    (paperThetaSchurObservationDefect_norm_le S) (paperThetaSchurObservationDefect_strong S) x

theorem paperThetaSchurFinite_moving_mask_tendsto (S : PaperThetaSchurFamily)
    (x : PaperThetaSchurSpace) (m : ℕ → LpCoordinateMask PaperThetaSchurMode) :
    Tendsto (fun N => paperThetaSchurObservationDefect S N (lpMaskedHistory x (m N)))
      atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ _ (norm_nonneg _)
    (paperThetaSchurObservationDefect_norm_le S) (paperThetaSchurObservationDefect_strong S) x m

theorem paperThetaSchurFinite_observation_attained (S : PaperThetaSchurFamily)
    (N : ℕ) (x : PaperThetaSchurSpace) :
    ∃ m : LpCoordinateMask PaperThetaSchurMode,
      ‖paperThetaSchurObservationDefect S N (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperThetaSchurObservationDefect S N) x :=
  lpSolidObservation_attained _ x

end
end RHTower.HedenmalmThetaSource
