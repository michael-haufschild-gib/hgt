import GaloisForLFunctions.RHTower.PaperLiNegativeSuppression
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Uniform masked observation of actual negative Li histories

Budget suppression holds for the entire solid hull of each full history,
unconditionally. The operator-norm criterion remains exactly RH.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry

theorem paperLiNegativeBudget_uniform_solidHull (x : PaperLiHistory) :
    TendstoUniformlyOn (fun N y => paperLiNegativeOperator (paperLiIncreasingBudget N) y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one
    (fun N => paperLiNegativeOperator_norm_le (paperLiIncreasingBudget N))
    paperLiNegativeOperator_budget_strong_tendsto x

theorem paperLiNegativeBudget_uniform_masks (x : PaperLiHistory) :
    TendstoUniformly (fun N m =>
      paperLiNegativeOperator (paperLiIncreasingBudget N) (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one
    (fun N => paperLiNegativeOperator_norm_le (paperLiIncreasingBudget N))
    paperLiNegativeOperator_budget_strong_tendsto x

theorem paperLiNegativeBudget_solidObservation_tendsto (x : PaperLiHistory) :
    Tendsto (fun N => lpSolidObservation (paperLiNegativeOperator (paperLiIncreasingBudget N)) x)
      atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one
    (fun N => paperLiNegativeOperator_norm_le (paperLiIncreasingBudget N))
    paperLiNegativeOperator_budget_strong_tendsto x

theorem paperLiNegativeBudget_moving_mask_tendsto (x : PaperLiHistory)
    (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperLiNegativeOperator (paperLiIncreasingBudget N)
      (lpMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one
    (fun N => paperLiNegativeOperator_norm_le (paperLiIncreasingBudget N))
    paperLiNegativeOperator_budget_strong_tendsto x m

theorem paperLiNegativeBudget_observation_attained (N : ℕ) (x : PaperLiHistory) :
    ∃ m : LpCoordinateMask ℕ,
      ‖paperLiNegativeOperator (paperLiIncreasingBudget N) (lpMaskedHistory x m)‖ =
        lpSolidObservation (paperLiNegativeOperator (paperLiIncreasingBudget N)) x :=
  lpSolidObservation_attained _ x

end
end RHTower
