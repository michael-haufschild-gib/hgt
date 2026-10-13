import GaloisForLFunctions.RHTower.PaperHurwitzPrefixSolidObservation
import GaloisForLFunctions.HTGeometry.LpSolidDiagonalObservation
import GaloisForLFunctions.HTGeometry.LpDisjointEnergy

/-! # Exact Hurwitz observations and retained/discarded energy

The original history simultaneously maximizes the full, retained and discarded
responses. Their squared observations obey an exact energy partition.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

theorem paperHurwitzObservationDefect_apply (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) (k : ℕ) :
    paperHurwitzObservationDefect t N x k =
      ((paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k : ℂ) - 1) * x k := by
  simp only [paperHurwitzObservationDefect, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperHurwitzResolvent_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply]
  ring

def paperHurwitzPrefixTail (t : ℝ) (N M : ℕ) : PaperHurwitzHistory →L[ℂ] PaperHurwitzHistory :=
  paperHurwitzObservationDefect t N - paperHurwitzPrefixDefect t N M

theorem paperHurwitzPrefixTail_apply (t : ℝ) (N M : ℕ) (x : PaperHurwitzHistory) (k : ℕ) :
    paperHurwitzPrefixTail t N M x k =
      (if k ≤ M then 0 else (paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k : ℂ) - 1) *
        x k := by
  simp only [paperHurwitzPrefixTail, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperHurwitzObservationDefect_apply, paperHurwitzPrefixDefect_apply]
  split_ifs <;> ring

theorem paperHurwitzResolvent_solidObservation (rho : ℂ) (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzResolvent rho) x = ‖paperHurwitzResolvent rho x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ _ (paperHurwitzResolvent_apply rho) x

theorem paperHurwitzDefect_solidObservation (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzObservationDefect t N) x = ‖paperHurwitzObservationDefect t N x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ _ (paperHurwitzObservationDefect_apply t N) x

theorem paperHurwitzPrefix_solidObservation (t : ℝ) (N M : ℕ) (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzPrefixDefect t N M) x = ‖paperHurwitzPrefixDefect t N M x‖ := by
  apply lpSolidObservation_eq_norm_of_coordinate_mul _
    (fun k => if k ≤ M then (paperHurwitzRegularizer (paperHurwitzApproachPoint t N) k : ℂ) - 1 else 0)
  intro y k
  rw [paperHurwitzPrefixDefect_apply]
  split_ifs <;> simp

theorem paperHurwitzTail_solidObservation (t : ℝ) (N M : ℕ) (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzPrefixTail t N M) x = ‖paperHurwitzPrefixTail t N M x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ _ (paperHurwitzPrefixTail_apply t N M) x

theorem paperHurwitzPrefix_observation_energy_split (t : ℝ) (N M : ℕ) (x : PaperHurwitzHistory) :
    lpSolidObservation (paperHurwitzPrefixDefect t N M) x ^ 2 +
      lpSolidObservation (paperHurwitzPrefixTail t N M) x ^ 2 =
        lpSolidObservation (paperHurwitzObservationDefect t N) x ^ 2 := by
  rw [paperHurwitzPrefix_solidObservation, paperHurwitzTail_solidObservation,
    paperHurwitzDefect_solidObservation]
  simp only [paperHurwitzPrefixTail, sub_apply,
    paperHurwitzPrefixDefect_eq_projection_comp, ContinuousLinearMap.comp_apply]
  exact paperCoordinateProjection_energy_split (M + 1) (paperHurwitzObservationDefect t N x)

theorem paperHurwitzPrefix_observation_monotone (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) :
    Monotone (fun M => lpSolidObservation (paperHurwitzPrefixDefect t N M) x) := by
  intro M L hML
  simp only [paperHurwitzPrefix_solidObservation]
  simp only [paperHurwitzPrefixDefect_eq_projection_comp,
    ContinuousLinearMap.comp_apply]
  exact norm_paperCoordinateProjection_monotone (paperHurwitzObservationDefect t N x)
    (by omega : M + 1 ≤ L + 1)

theorem paperHurwitzTail_observation_antitone (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) :
    Antitone (fun M => lpSolidObservation (paperHurwitzPrefixTail t N M) x) := by
  intro M L hML
  simp only [paperHurwitzTail_solidObservation]
  simp only [paperHurwitzPrefixTail, sub_apply,
    paperHurwitzPrefixDefect_eq_projection_comp, ContinuousLinearMap.comp_apply]
  exact norm_paperCoordinateTail_antitone (paperHurwitzObservationDefect t N x)
    (by omega : M + 1 ≤ L + 1)

theorem paperHurwitzPrefix_observation_tendsto (t : ℝ) (N : ℕ) (x : PaperHurwitzHistory) :
    Tendsto (fun M => lpSolidObservation (paperHurwitzPrefixDefect t N M) x)
      atTop (𝓝 (lpSolidObservation (paperHurwitzObservationDefect t N) x)) := by
  simp only [paperHurwitzPrefix_solidObservation, paperHurwitzDefect_solidObservation]
  simpa only [paperHurwitzPrefixDefect_eq_projection_comp, ContinuousLinearMap.comp_apply] using
    ((tendsto_add_atTop_iff_nat 1).mpr
      (tendsto_paperCoordinateProjection (paperHurwitzObservationDefect t N x))).norm

theorem paperHurwitzPrefix_uniform_solidHull_iff {A : Type*} (l : Filter A)
    (t : A → ℝ) (N M : A → ℕ) (x : PaperHurwitzHistory) :
    TendstoUniformlyOn (fun a y => paperHurwitzPrefixDefect (t a) (N a) (M a) y)
      (fun _ => 0) l (lpSolidHull x) ↔
      Tendsto (fun a => paperHurwitzPrefixDefect (t a) (N a) (M a) x) l (𝓝 0) := by
  apply tendstoUniformlyOn_lpSolidHull_coordinate_mul_iff _
    (fun a k => if k ≤ M a then
      (paperHurwitzRegularizer (paperHurwitzApproachPoint (t a) (N a)) k : ℂ) - 1 else 0)
  intro a y k
  rw [paperHurwitzPrefixDefect_apply]
  split_ifs <;> simp

end
end RHTower
