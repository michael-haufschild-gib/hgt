import GaloisForLFunctions.RHTower.PaperDeningerFiniteCurvature
import GaloisForLFunctions.HTGeometry.HilbertTruncationNorm
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Masked full histories of arithmetic mate curvature

The largest fixed-history observation of the finite curvature error vanishes
even off the critical line, where its operator norm stays exactly one.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

def paperDeningerObservationDefect (s : ℂ) (N : ℕ) : PaperCornerSpace →L[ℂ] PaperCornerSpace :=
  paperDeningerMateOperator s - paperDeningerFiniteOperator s N

theorem paperDeningerObservationDefect_norm_le (s : ℂ) (N : ℕ) :
    ‖paperDeningerObservationDefect s N‖ ≤ ‖paperDeningerMateOperator s‖ :=
  norm_sub_hsTruncation_le_norm _ _ _

/-- The old lower bound is sharp at every finite cutoff. -/
theorem paperDeningerObservationDefect_norm (s : ℂ) (N : ℕ) :
    ‖paperDeningerObservationDefect s N‖ = if s.re = 1 / 2 then 0 else 1 :=
  le_antisymm ((paperDeningerObservationDefect_norm_le s N).trans_eq
    (paperDeningerMateOperator_norm s)) (paperDeningerFiniteOperator_gap s N)

theorem paperDeningerObservationDefect_strong (s : ℂ) (x : PaperCornerSpace) :
    Tendsto (fun N => paperDeningerObservationDefect s N x) atTop (𝓝 0) := by
  simpa only [paperDeningerObservationDefect, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperDeningerMateOperator s x)).sub
      (paperDeningerFiniteOperator_strong_tendsto s x)

theorem paperDeningerFinite_uniform_solidHull (s : ℂ) (x : PaperCornerSpace) :
    TendstoUniformlyOn (fun N y => paperDeningerObservationDefect s N y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ _ (norm_nonneg _)
    (paperDeningerObservationDefect_norm_le s) (paperDeningerObservationDefect_strong s) x

theorem paperDeningerFinite_uniform_masks (s : ℂ) (x : PaperCornerSpace) :
    TendstoUniformly (fun N m => paperDeningerObservationDefect s N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ _ (norm_nonneg _)
    (paperDeningerObservationDefect_norm_le s) (paperDeningerObservationDefect_strong s) x

theorem paperDeningerFinite_solidObservation_tendsto (s : ℂ) (x : PaperCornerSpace) :
    Tendsto (fun N => lpSolidObservation (paperDeningerObservationDefect s N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ _ (norm_nonneg _)
    (paperDeningerObservationDefect_norm_le s) (paperDeningerObservationDefect_strong s) x

theorem paperDeningerFinite_moving_mask_tendsto (s : ℂ) (x : PaperCornerSpace)
    (m : ℕ → LpCoordinateMask (ℕ × Fin 2)) :
    Tendsto (fun N => paperDeningerObservationDefect s N (lpMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ _ (norm_nonneg _)
    (paperDeningerObservationDefect_norm_le s) (paperDeningerObservationDefect_strong s) x m

theorem paperDeningerFinite_observation_attained (s : ℂ) (N : ℕ) (x : PaperCornerSpace) :
    ∃ m : LpCoordinateMask (ℕ × Fin 2),
      ‖paperDeningerObservationDefect s N (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperDeningerObservationDefect s N) x :=
  lpSolidObservation_attained _ x

end
end RHTower
