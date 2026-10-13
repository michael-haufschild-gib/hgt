import GaloisForLFunctions.RHTower.PaperLiNegativeCutoffs
import GaloisForLFunctions.RHTower.PaperLiSolidObservation
import GaloisForLFunctions.HTGeometry.PaperCoordinateTail
import GaloisForLFunctions.HTGeometry.LpSolidObservationOrder

/-! # Complete masked observation of negative Li cutoffs

Fixed-budget prefixes recover the full operator uniformly on each solid history
hull, with error norm equal to the full operator norm at every depth. Increasing
budgets suppress all prefixes and masks simultaneously, without an RH premise.
-/

namespace RHTower
noncomputable section
open Classical Filter Topology GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem paperLiNegativePrefix_eq_projection_comp (b : PaperLiBudget) (N : ℕ) :
    paperLiNegativePrefix b N = paperCoordinateProjection N ∘L paperLiNegativeOperator b := by
  apply ContinuousLinearMap.ext
  intro x
  ext n
  simp only [ContinuousLinearMap.comp_apply, paperLiNegativePrefix_apply,
    paperCoordinateProjection_coordinate]

theorem paperLiNegativePrefix_norm_apply_le_full (b : PaperLiBudget) (N : ℕ)
    (x : PaperLiHistory) :
    ‖paperLiNegativePrefix b N x‖ ≤ ‖paperLiNegativeOperator b x‖ := by
  rw [paperLiNegativePrefix_eq_projection_comp, ContinuousLinearMap.comp_apply]
  exact norm_paperCoordinateProjection_apply_le _ _

def paperLiCutoffError (b : PaperLiBudget) (N : ℕ) : PaperLiHistory →L[ℂ] PaperLiHistory :=
  paperLiNegativeOperator b - paperLiNegativePrefix b N

theorem paperLiCutoffError_norm_eq_operator (b : PaperLiBudget) (N : ℕ) :
    ‖paperLiCutoffError b N‖ = ‖paperLiNegativeOperator b‖ := by
  apply le_antisymm
  · simpa only [paperLiCutoffError, paperLiNegativePrefix_eq_projection_comp] using
      norm_sub_paperCoordinateProjection_comp_le (paperLiNegativeOperator b) N
  · simpa only [paperLiCutoffError, paperLiNegativeOperator_norm] using paperLiNegativePrefix_gap b N

theorem paperLiCutoffError_norm (b : PaperLiBudget) (N : ℕ) :
    ‖paperLiCutoffError b N‖ = if RiemannHypothesis then 0 else 1 := by
  rw [paperLiCutoffError_norm_eq_operator, paperLiNegativeOperator_norm]

theorem paperLiCutoffError_traceCost (b : PaperLiBudget) (N : ℕ) :
    compactOperatorTraceCost PaperLiHistory (paperLiCutoffError b N) =
      if RiemannHypothesis then 0 else ∞ := by
  let K : compactOperatorStarAlgebra PaperLiHistory :=
    ⟨paperLiNegativePrefix b N, paperLiNegativePrefix_compact b N⟩
  simpa [paperLiCutoffError, sub_eq_add_neg, K] using
    paperLiNegativeOperator_traceCost_add_compact b (-K)

theorem paperLiCutoffError_strong (b : PaperLiBudget) (x : PaperLiHistory) :
    Tendsto (fun N => paperLiCutoffError b N x) atTop (𝓝 0) := by
  simpa only [paperLiCutoffError, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperLiNegativeOperator b x)).sub
      (paperLiNegativePrefix_strong_tendsto b x)

theorem paperLiCutoffError_norm_le (b : PaperLiBudget) (N : ℕ) :
    ‖paperLiCutoffError b N‖ ≤ 1 := by
  rw [paperLiCutoffError_norm_eq_operator]
  exact paperLiNegativeOperator_norm_le b

theorem paperLiCutoff_uniform_solidHull (b : PaperLiBudget) (x : PaperLiHistory) :
    TendstoUniformlyOn (fun N y => paperLiCutoffError b N y) (fun _ => 0)
      atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one (paperLiCutoffError_norm_le b)
    (paperLiCutoffError_strong b) x

theorem paperLiCutoff_uniform_masks (b : PaperLiBudget) (x : PaperLiHistory) :
    TendstoUniformly (fun N m => paperLiCutoffError b N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one (paperLiCutoffError_norm_le b)
    (paperLiCutoffError_strong b) x

theorem paperLiCutoff_solidObservation_tendsto (b : PaperLiBudget) (x : PaperLiHistory) :
    Tendsto (fun N => lpSolidObservation (paperLiCutoffError b N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one (paperLiCutoffError_norm_le b)
    (paperLiCutoffError_strong b) x

theorem paperLiCutoff_moving_mask_tendsto (b : PaperLiBudget) (x : PaperLiHistory)
    (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperLiCutoffError b N (lpMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one (paperLiCutoffError_norm_le b)
    (paperLiCutoffError_strong b) x m

theorem paperLiCutoff_observation_attained (b : PaperLiBudget) (N : ℕ) (x : PaperLiHistory) :
    ∃ m : LpCoordinateMask ℕ, ‖paperLiCutoffError b N (lpMaskedHistory x m)‖ =
      lpSolidObservation (paperLiCutoffError b N) x := lpSolidObservation_attained _ x

theorem paperLiNegativeBudget_prefix_uniform_masks (x : PaperLiHistory) :
    TendstoUniformly (fun m (q : ℕ × LpCoordinateMask ℕ) =>
      paperLiNegativePrefix (paperLiIncreasingBudget m) q.1 (lpMaskedHistory x q.2))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory_of_norm_le _
    (fun m => paperLiNegativeOperator (paperLiIncreasingBudget m)) x
    (fun m => paperLiNegativePrefix_norm_apply_le_full (paperLiIncreasingBudget m))
    (paperLiNegativeBudget_uniform_masks x)

theorem paperLiNegativeBudget_prefix_uniform_solidObservation (x : PaperLiHistory) :
    TendstoUniformly (fun m N =>
      lpSolidObservation (paperLiNegativePrefix (paperLiIncreasingBudget m) N) x)
      (fun _ => 0) atTop :=
  tendstoUniformly_lpSolidObservation_of_norm_le _
    (fun m => paperLiNegativeOperator (paperLiIncreasingBudget m)) x
    (fun m => paperLiNegativePrefix_norm_apply_le_full (paperLiIncreasingBudget m))
    (paperLiNegativeBudget_solidObservation_tendsto x)

theorem paperLiNegativeBudget_prefix_moving_mask_tendsto (x : PaperLiHistory)
    (N : ℕ → ℕ) (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun j => paperLiNegativePrefix (paperLiIncreasingBudget j) (N j)
      (lpMaskedHistory x (m j))) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun j =>
    paperLiNegativePrefix_norm_apply_le_full (paperLiIncreasingBudget j) (N j) _)
  simpa only [norm_zero] using (paperLiNegativeBudget_moving_mask_tendsto x m).norm

end
end RHTower
