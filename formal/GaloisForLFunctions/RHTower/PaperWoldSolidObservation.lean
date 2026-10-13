import GaloisForLFunctions.RHTower.PaperWoldExactNorm
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Complete masked-history observations of the critical Wold approach

The operator defect keeps norm one and infinite compact-ideal cost, while
its largest response over all masks of each fixed history tends to zero.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperWoldCompositeObservationDefect (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldCriticalCompositeOperator - paperWoldCompositeApproach N

theorem paperWoldCompositeObservationDefect_norm (N : ℕ) :
    ‖paperWoldCompositeObservationDefect N‖ = 1 :=
  paperWoldCompositeOperator_critical_difference_norm (paperWoldCompositeApproachExponent N)

theorem paperWoldCompositeObservationDefect_traceCost (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositeObservationDefect N) = ∞ :=
  paperWoldCompositeOperator_critical_difference_traceCost (paperWoldCompositeApproachExponent N)

theorem paperWoldCompositeObservationDefect_strong (x : PaperWoldHistory) :
    Tendsto (fun N => paperWoldCompositeObservationDefect N x) atTop (𝓝 0) := by
  simpa only [paperWoldCompositeObservationDefect, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperWoldCriticalCompositeOperator x)).sub
      (paperWoldCompositeApproach_strong_tendsto x)

theorem paperWoldCompositeApproach_uniform_solidHull (x : PaperWoldHistory) :
    TendstoUniformlyOn (fun N y => paperWoldCompositeObservationDefect N y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one
    (fun N => (paperWoldCompositeObservationDefect_norm N).le)
    paperWoldCompositeObservationDefect_strong x

theorem paperWoldCompositeApproach_uniform_masks (x : PaperWoldHistory) :
    TendstoUniformly (fun N m => paperWoldCompositeObservationDefect N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one
    (fun N => (paperWoldCompositeObservationDefect_norm N).le)
    paperWoldCompositeObservationDefect_strong x

/-- Even the attained worst coordinate mask of a fixed history loses the complete defect. -/
theorem paperWoldCompositeApproach_solidObservation_tendsto (x : PaperWoldHistory) :
    Tendsto (fun N => lpSolidObservation (paperWoldCompositeObservationDefect N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one
    (fun N => (paperWoldCompositeObservationDefect_norm N).le)
    paperWoldCompositeObservationDefect_strong x

theorem paperWoldCompositeApproach_moving_mask_tendsto (x : PaperWoldHistory)
    (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperWoldCompositeObservationDefect N (lpMaskedHistory x (m N)))
      atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one
    (fun N => (paperWoldCompositeObservationDefect_norm N).le)
    paperWoldCompositeObservationDefect_strong x m

theorem paperWoldCompositeObservation_attained (N : ℕ) (x : PaperWoldHistory) :
    ∃ m : LpCoordinateMask ℕ,
      ‖paperWoldCompositeObservationDefect N (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperWoldCompositeObservationDefect N) x :=
  lpSolidObservation_attained _ x

end
end RHTower
