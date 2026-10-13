import GaloisForLFunctions.RHTower.PaperHurwitzObservationScale
import GaloisForLFunctions.RHTower.PaperHurwitzSolidObservation
import GaloisForLFunctions.HTGeometry.LpSolidObservationOrder

/-! # Simultaneous observation of every Hurwitz prefix

All prefix lengths and all coordinate masks of each fixed full history obey
one uniform decay bound. The linear and quadratic prefix norm gaps persist.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

theorem paperHurwitzPrefixDefect_eq_projection_comp (t : ℝ) (N M : ℕ) :
    paperHurwitzPrefixDefect t N M =
      paperCoordinateProjection (M + 1) ∘L paperHurwitzObservationDefect t N := by
  apply ContinuousLinearMap.ext
  intro f
  ext k
  simp only [ContinuousLinearMap.comp_apply, paperHurwitzObservationDefect,
    paperHurwitzPrefixDefect_apply, paperCoordinateProjection_coordinate,
    Nat.lt_succ_iff, sub_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
    lp.coeFn_sub, Pi.sub_apply, paperHurwitzResolvent_apply]
  split_ifs <;> ring

theorem paperHurwitzPrefixDefect_norm_apply_le_full (t : ℝ) (N M : ℕ)
    (x : PaperHurwitzHistory) :
    ‖paperHurwitzPrefixDefect t N M x‖ ≤ ‖paperHurwitzObservationDefect t N x‖ := by
  rw [paperHurwitzPrefixDefect_eq_projection_comp, ContinuousLinearMap.comp_apply]
  exact norm_paperCoordinateProjection_apply_le _ _

theorem paperHurwitzPrefix_solidObservation_le_full (t : ℝ) (N M : ℕ)
    (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzPrefixDefect t N M) x ≤
      lpSolidObservation (paperHurwitzObservationDefect t N) x :=
  lpSolidObservation_mono _ _ x (fun y _ => paperHurwitzPrefixDefect_norm_apply_le_full t N M y)

theorem paperHurwitzPrefix_uniform_all_masks (t : ℝ) (x : PaperHurwitzHistory) :
    TendstoUniformly (fun N (q : ℕ × LpCoordinateMask ℕ) =>
      paperHurwitzPrefixDefect t N q.1 (lpMaskedHistory x q.2)) (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory_of_norm_le _ (paperHurwitzObservationDefect t) x
    (paperHurwitzPrefixDefect_norm_apply_le_full t) (paperHurwitzApproach_uniform_masks t x)

theorem paperHurwitzPrefix_uniform_solidObservation (t : ℝ) (x : PaperHurwitzHistory) :
    TendstoUniformly (fun N M => lpSolidObservation (paperHurwitzPrefixDefect t N M) x)
      (fun _ => 0) atTop :=
  tendstoUniformly_lpSolidObservation_of_norm_le _ (paperHurwitzObservationDefect t) x
    (paperHurwitzPrefixDefect_norm_apply_le_full t)
    (paperHurwitzApproach_solidObservation_tendsto t x)

theorem paperHurwitzPrefix_moving_mask_tendsto (t : ℝ) (x : PaperHurwitzHistory)
    (M : ℕ → ℕ) (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperHurwitzPrefixDefect t N (M N) (lpMaskedHistory x (m N)))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => paperHurwitzPrefixDefect_norm_apply_le_full t N (M N) _)
  simpa only [norm_zero] using (paperHurwitzApproach_moving_mask_tendsto t x m).norm

theorem paperHurwitzPrefix_observation_attained (t : ℝ) (N M : ℕ) (x : PaperHurwitzHistory) :
    ∃ m : LpCoordinateMask ℕ, ‖paperHurwitzPrefixDefect t N M (lpMaskedHistory x m)‖ =
      lpSolidObservation (paperHurwitzPrefixDefect t N M) x := lpSolidObservation_attained _ x

theorem paperHurwitzPrefix_masked_norm_separation (t : ℝ) (x : PaperHurwitzHistory) :
    (∀ N, ‖paperHurwitzPrefixDefect t N (N + 3)‖ = 9 / 25) ∧
    Tendsto (fun N => ‖paperHurwitzPrefixDefect t N ((N + 3) ^ 2)‖) atTop (𝓝 1) ∧
    TendstoUniformly (fun N M => lpSolidObservation (paperHurwitzPrefixDefect t N M) x)
      (fun _ => 0) atTop :=
  ⟨norm_paperHurwitzPrefixDefect_linear_one t, paperHurwitzPrefixDefect_square_tendsto t,
    paperHurwitzPrefix_uniform_solidObservation t x⟩

end
end RHTower
