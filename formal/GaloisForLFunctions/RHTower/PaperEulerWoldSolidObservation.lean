import GaloisForLFunctions.RHTower.PaperEulerWoldDepthCompression
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Full masked observations of the Euler/Wold depth completion

Every native lane admits uniform finite-prefix recovery on each fixed solid
history hull, including the endpoint and transverse lanes with persistent gaps.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

def paperEulerWoldObservationDefect (a b d : ℝ) (c : ℂ) (N : ℕ) :
    VecSeq ℂ →L[ℂ] VecSeq ℂ :=
  paperEulerWoldHistoryOperator a b d c -
    paperCoordinateCompression (paperEulerWoldHistoryOperator a b d c) N

theorem paperEulerWoldObservationDefect_norm_le (a b d : ℝ) (c : ℂ) (N : ℕ) :
    ‖paperEulerWoldObservationDefect a b d c N‖ ≤ 2 * ‖paperEulerWoldHistoryOperator a b d c‖ := by
  exact (norm_sub_le _ _).trans (by
    have h := norm_paperCoordinateCompression_le (paperEulerWoldHistoryOperator a b d c) N
    linarith)

theorem paperEulerWoldObservationDefect_strong (a b d : ℝ) (c : ℂ) (x : VecSeq ℂ) :
    Tendsto (fun N => paperEulerWoldObservationDefect a b d c N x) atTop (𝓝 0) := by
  simpa only [paperEulerWoldObservationDefect, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperEulerWoldHistoryOperator a b d c x)).sub
      (paperEulerWoldHistoryOperator_compression_tendsto a b d c x)

theorem paperEulerWoldDepth_uniform_solidHull (a b d : ℝ) (c : ℂ) (x : VecSeq ℂ) :
    TendstoUniformlyOn (fun N y => paperEulerWoldObservationDefect a b d c N y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ _ (by positivity)
    (paperEulerWoldObservationDefect_norm_le a b d c)
    (paperEulerWoldObservationDefect_strong a b d c) x

theorem paperEulerWoldDepth_uniform_masks (a b d : ℝ) (c : ℂ) (x : VecSeq ℂ) :
    TendstoUniformly (fun N m => paperEulerWoldObservationDefect a b d c N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ _ (by positivity)
    (paperEulerWoldObservationDefect_norm_le a b d c)
    (paperEulerWoldObservationDefect_strong a b d c) x

theorem paperEulerWoldDepth_solidObservation_tendsto (a b d : ℝ) (c : ℂ) (x : VecSeq ℂ) :
    Tendsto (fun N => lpSolidObservation (paperEulerWoldObservationDefect a b d c N) x)
      atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ _ (by positivity)
    (paperEulerWoldObservationDefect_norm_le a b d c)
    (paperEulerWoldObservationDefect_strong a b d c) x

theorem paperEulerWoldDepth_moving_mask_tendsto (a b d : ℝ) (c : ℂ) (x : VecSeq ℂ)
    (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperEulerWoldObservationDefect a b d c N (lpMaskedHistory x (m N)))
      atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ _ (by positivity)
    (paperEulerWoldObservationDefect_norm_le a b d c)
    (paperEulerWoldObservationDefect_strong a b d c) x m

theorem paperEulerWoldDepth_observation_attained (a b d : ℝ) (c : ℂ) (N : ℕ) (x : VecSeq ℂ) :
    ∃ m : LpCoordinateMask ℕ,
      ‖paperEulerWoldObservationDefect a b d c N (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperEulerWoldObservationDefect a b d c N) x :=
  lpSolidObservation_attained _ x

end
end RHTower
