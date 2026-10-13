import GaloisForLFunctions.RHTower.PaperLiCutoffSolidObservation
import GaloisForLFunctions.HTGeometry.LpSolidDiagonalObservation
import GaloisForLFunctions.HTGeometry.LpDisjointEnergy

/-! # Exact observed and discarded negative Li energy

No coordinate mask improves the response beyond the original history. Finite
prefixes split its total observed energy exactly, and recover it monotonically.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

theorem paperLiCutoffError_apply (b : PaperLiBudget) (N : ℕ) (x : PaperLiHistory) (n : ℕ) :
    paperLiCutoffError b N x n = (if n < N then 0 else (paperLiNegativeWeight b n : ℂ)) * x n := by
  simp only [paperLiCutoffError, sub_apply, lp.coeFn_sub, Pi.sub_apply,
    paperLiNegativePrefix_apply, paperLiNegativeOperator_apply]
  split_ifs <;> ring

theorem paperLiNegativeOperator_solidObservation (b : PaperLiBudget) (x : PaperLiHistory) :
    lpSolidObservation (paperLiNegativeOperator b) x = ‖paperLiNegativeOperator b x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ _ (paperLiNegativeOperator_apply b) x

theorem paperLiNegativePrefix_solidObservation (b : PaperLiBudget) (N : ℕ) (x : PaperLiHistory) :
    lpSolidObservation (paperLiNegativePrefix b N) x = ‖paperLiNegativePrefix b N x‖ := by
  apply lpSolidObservation_eq_norm_of_coordinate_mul _
    (fun n => if n < N then (paperLiNegativeWeight b n : ℂ) else 0)
  intro y n
  rw [paperLiNegativePrefix_apply, paperLiNegativeOperator_apply]
  split_ifs <;> simp

theorem paperLiCutoffError_solidObservation (b : PaperLiBudget) (N : ℕ) (x : PaperLiHistory) :
    lpSolidObservation (paperLiCutoffError b N) x = ‖paperLiCutoffError b N x‖ :=
  lpSolidObservation_eq_norm_of_coordinate_mul _ _ (paperLiCutoffError_apply b N) x

theorem paperLiPrefix_observation_energy_split (b : PaperLiBudget) (N : ℕ) (x : PaperLiHistory) :
    lpSolidObservation (paperLiNegativePrefix b N) x ^ 2 +
      lpSolidObservation (paperLiCutoffError b N) x ^ 2 =
        lpSolidObservation (paperLiNegativeOperator b) x ^ 2 := by
  rw [paperLiNegativePrefix_solidObservation, paperLiCutoffError_solidObservation,
    paperLiNegativeOperator_solidObservation]
  simp only [paperLiCutoffError, sub_apply,
    paperLiNegativePrefix_eq_projection_comp, ContinuousLinearMap.comp_apply]
  exact paperCoordinateProjection_energy_split N (paperLiNegativeOperator b x)

theorem paperLiPrefix_observation_monotone (b : PaperLiBudget) (x : PaperLiHistory) :
    Monotone (fun N => lpSolidObservation (paperLiNegativePrefix b N) x) := by
  simp only [paperLiNegativePrefix_solidObservation]
  simpa only [paperLiNegativePrefix_eq_projection_comp,
    ContinuousLinearMap.comp_apply] using norm_paperCoordinateProjection_monotone (paperLiNegativeOperator b x)

theorem paperLiCutoff_observation_antitone (b : PaperLiBudget) (x : PaperLiHistory) :
    Antitone (fun N => lpSolidObservation (paperLiCutoffError b N) x) := by
  simp only [paperLiCutoffError_solidObservation]
  simpa only [paperLiCutoffError, sub_apply,
    paperLiNegativePrefix_eq_projection_comp, ContinuousLinearMap.comp_apply] using
      norm_paperCoordinateTail_antitone (paperLiNegativeOperator b x)

theorem paperLiPrefix_observation_tendsto (b : PaperLiBudget) (x : PaperLiHistory) :
    Tendsto (fun N => lpSolidObservation (paperLiNegativePrefix b N) x)
      atTop (𝓝 (lpSolidObservation (paperLiNegativeOperator b) x)) := by
  simpa only [paperLiNegativePrefix_solidObservation, paperLiNegativeOperator_solidObservation] using
    (paperLiNegativePrefix_strong_tendsto b x).norm

theorem paperLiNegative_uniform_solidHull_iff {A : Type*} (l : Filter A)
    (b : A → PaperLiBudget) (x : PaperLiHistory) :
    TendstoUniformlyOn (fun a y => paperLiNegativeOperator (b a) y) (fun _ => 0) l (lpSolidHull x) ↔
      Tendsto (fun a => paperLiNegativeOperator (b a) x) l (𝓝 0) :=
  tendstoUniformlyOn_lpSolidHull_coordinate_mul_iff _ _
    (fun a => paperLiNegativeOperator_apply (b a)) x

theorem paperLiCutoff_uniform_solidHull_iff {A : Type*} (l : Filter A)
    (b : A → PaperLiBudget) (N : A → ℕ) (x : PaperLiHistory) :
    TendstoUniformlyOn (fun a y => paperLiCutoffError (b a) (N a) y) (fun _ => 0) l (lpSolidHull x) ↔
      Tendsto (fun a => paperLiCutoffError (b a) (N a) x) l (𝓝 0) :=
  tendstoUniformlyOn_lpSolidHull_coordinate_mul_iff _ _
    (fun a => paperLiCutoffError_apply (b a) (N a)) x

end
end RHTower
