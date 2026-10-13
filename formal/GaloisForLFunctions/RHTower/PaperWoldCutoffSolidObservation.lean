import GaloisForLFunctions.RHTower.PaperWoldCompositeCutoffs
import GaloisForLFunctions.RHTower.PaperWoldExactNorm
import GaloisForLFunctions.HTGeometry.PaperCoordinateTail
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Exact finite-cutoff errors and complete masked Wold observations

The upper-triangular source makes a square cutoff an input-prefix truncation.
Its error has norm exactly one and infinite paper ideal cost at every depth,
while all masks of each fixed full history recover the completed operator.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem paperWoldCriticalCompositeCutoff_eq_comp (N : ℕ) :
    paperWoldCriticalCompositeCutoff N =
      paperWoldCriticalCompositeOperator ∘L paperCoordinateProjection N := by
  apply HasLpMatrix.ext (K := fun n j =>
    if n < N ∧ j < N then paperWoldCompositeEntry (1 / 2) n j else 0)
  · exact fun n j => paperWoldCriticalCompositeCutoff_single N n j
  · intro n j
    change paperWoldCriticalCompositeOperator
      (paperCoordinateProjection N (lp.single 2 j (1 : ℂ))) n = _
    rw [paperCoordinateProjection_single]
    by_cases hj : j < N
    · rw [if_pos hj, paperWoldCriticalCompositeOperator_single]
      simp only [hj, and_true]
      by_cases hn : n < N
      · rw [if_pos hn]
      · rw [if_neg hn]
        simp only [paperWoldCompositeEntry, paperWoldDirectedKernel,
          if_neg (by omega : ¬ (2 * n + 2 < 2 * j + 2))]
    · rw [if_neg hj, map_zero]
      simp only [lp.coeFn_zero, Pi.zero_apply, hj, and_false, if_false]

theorem paperWoldCriticalCompositeCutoff_norm_le_one (N : ℕ) :
    ‖paperWoldCriticalCompositeCutoff N‖ ≤ 1 := by
  rw [paperWoldCriticalCompositeCutoff_eq_comp]
  have h := paperWoldCriticalCompositeOperator.opNorm_comp_le (paperCoordinateProjection N)
  rw [paperWoldCriticalCompositeOperator_norm, one_mul] at h
  exact h.trans (norm_paperCoordinateProjection_le N)

def paperWoldCutoffError (N : ℕ) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N

theorem paperWoldCutoffError_norm (N : ℕ) : ‖paperWoldCutoffError N‖ = 1 := by
  apply le_antisymm
  · simpa only [paperWoldCutoffError, paperWoldCriticalCompositeCutoff_eq_comp,
      paperWoldCriticalCompositeOperator_norm] using
      norm_sub_comp_paperCoordinateProjection_le paperWoldCriticalCompositeOperator N
  · simpa only [paperWoldCriticalCompositeOperator_compactIdealDistance, paperWoldCutoffError] using
      compactIdealDistance_le paperWoldCriticalCompositeOperator (paperWoldCriticalCompositeCutoff N)
        (paperWoldCriticalCompositeCutoff_compact N)

theorem paperWoldCutoffError_traceCost (N : ℕ) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCutoffError N) = ∞ := by
  let K : compactOperatorStarAlgebra PaperWoldHistory :=
    ⟨paperWoldCriticalCompositeCutoff N, paperWoldCriticalCompositeCutoff_compact N⟩
  simpa [paperWoldCutoffError, sub_eq_add_neg, K] using
    paperWoldCriticalCompositeOperator_add_compact_traceCost (-K)

theorem paperWoldCutoffError_strong (x : PaperWoldHistory) :
    Tendsto (fun N => paperWoldCutoffError N x) atTop (𝓝 0) := by
  simpa only [paperWoldCutoffError, sub_apply, sub_self] using
    (tendsto_const_nhds (x := paperWoldCriticalCompositeOperator x)).sub
      (paperWoldCriticalCompositeCutoff_strong_tendsto x)

theorem paperWoldCutoff_uniform_solidHull (x : PaperWoldHistory) :
    TendstoUniformlyOn (fun N y => paperWoldCutoffError N y) (fun _ => 0)
      atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one (fun N => (paperWoldCutoffError_norm N).le)
    paperWoldCutoffError_strong x

theorem paperWoldCutoff_uniform_masks (x : PaperWoldHistory) :
    TendstoUniformly (fun N m => paperWoldCutoffError N (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one (fun N => (paperWoldCutoffError_norm N).le)
    paperWoldCutoffError_strong x

theorem paperWoldCutoff_solidObservation_tendsto (x : PaperWoldHistory) :
    Tendsto (fun N => lpSolidObservation (paperWoldCutoffError N) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one (fun N => (paperWoldCutoffError_norm N).le)
    paperWoldCutoffError_strong x

theorem paperWoldCutoff_moving_mask_tendsto (x : PaperWoldHistory) (m : ℕ → LpCoordinateMask ℕ) :
    Tendsto (fun N => paperWoldCutoffError N (lpMaskedHistory x (m N))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one (fun N => (paperWoldCutoffError_norm N).le)
    paperWoldCutoffError_strong x m

theorem paperWoldCutoff_observation_attained (N : ℕ) (x : PaperWoldHistory) :
    ∃ m : LpCoordinateMask ℕ, ‖paperWoldCutoffError N (lpMaskedHistory x m)‖ =
      lpSolidObservation (paperWoldCutoffError N) x := lpSolidObservation_attained _ x

theorem paperWoldCutoff_masked_completion (x : PaperWoldHistory) :
    (∀ N, ‖paperWoldCutoffError N‖ = 1) ∧
    (∀ N, compactOperatorTraceCost PaperWoldHistory (paperWoldCutoffError N) = ∞) ∧
    Tendsto (fun N => lpSolidObservation (paperWoldCutoffError N) x) atTop (𝓝 0) :=
  ⟨paperWoldCutoffError_norm, paperWoldCutoffError_traceCost, paperWoldCutoff_solidObservation_tendsto x⟩

end
end RHTower
