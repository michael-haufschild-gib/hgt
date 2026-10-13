import GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Complete masked-history observations at the Hurwitz wall

All coordinate masks of one fixed full history lose the approaching wall
defect uniformly, although its operator norm and compact-ideal cost persist.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperHurwitzObservationDefect (t : ℝ) (N : ℕ) : PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1

theorem paperHurwitzObservationDefect_norm (t : ℝ) (N : ℕ) :
    ‖paperHurwitzObservationDefect t N‖ = 1 := paperHurwitzApproachPoint_norm_gap t N

theorem paperHurwitzObservationDefect_traceCost (t : ℝ) (N : ℕ) :
    compactOperatorTraceCost PaperHurwitzHistory (paperHurwitzObservationDefect t N) = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).mpr
  intro hc
  have hw : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have he := paperHurwitzResolvent_compact_sub_iff (paperHurwitzApproachPoint t N) (1 / 2)
  rw [paperHurwitzResolvent_of_wall hw] at he
  exact paperHurwitzApproachPoint_off_wall t N ((he.mp hc).mpr hw)

theorem paperHurwitzObservationDefect_strong (t : ℝ) (x : PaperHurwitzHistory) :
    Tendsto (fun N => paperHurwitzObservationDefect t N x) atTop (𝓝 0) := by
  simpa only [paperHurwitzObservationDefect, sub_apply, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply, sub_self] using
    (tendsto_paperHurwitzApproachPoint_strong t x).sub (tendsto_const_nhds (x := x))

theorem paperHurwitzApproach_uniform_solidHull (t : ℝ) (x : PaperHurwitzHistory) :
    TendstoUniformlyOn (fun N y => paperHurwitzObservationDefect t N y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one
    (fun N => (paperHurwitzObservationDefect_norm t N).le)
    (paperHurwitzObservationDefect_strong t) x

theorem paperHurwitzApproach_uniform_masks (t : ℝ) (x : PaperHurwitzHistory) :
    TendstoUniformly (fun N m => paperHurwitzObservationDefect t N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one
    (fun N => (paperHurwitzObservationDefect_norm t N).le)
    (paperHurwitzObservationDefect_strong t) x

theorem paperHurwitzApproach_solidObservation_tendsto (t : ℝ) (x : PaperHurwitzHistory) :
    Tendsto (fun N => lpSolidObservation (paperHurwitzObservationDefect t N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one
    (fun N => (paperHurwitzObservationDefect_norm t N).le)
    (paperHurwitzObservationDefect_strong t) x

theorem paperHurwitzApproach_moving_mask_tendsto (t : ℝ) (x : PaperHurwitzHistory)
    (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperHurwitzObservationDefect t N (lpMaskedHistory x (m N)))
      atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one
    (fun N => (paperHurwitzObservationDefect_norm t N).le)
    (paperHurwitzObservationDefect_strong t) x m

theorem paperHurwitzObservation_attained (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) :
    ∃ m : LpCoordinateMask ℕ,
      ‖paperHurwitzObservationDefect t N (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperHurwitzObservationDefect t N) x :=
  lpSolidObservation_attained _ x

end
end RHTower
