import GaloisForLFunctions.RHTower.PaperWoldExactNorm

/-! # Exact norm separation for every literal finite composite square

The omitted entries form another admissible Hardy-dominated mask. Consequently
the complete cutoff error has norm exactly one, although cutoff norms tend to one.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem paperWoldCriticalCompositeCutoff_norm_le_one (N : ℕ) :
    ‖paperWoldCriticalCompositeCutoff N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  exact (norm_coordTruncation_apply_le _ _).trans
    ((paperWoldCriticalCompositeOperator.le_opNorm _).trans
      (mul_le_mul paperWoldCriticalCompositeOperator_norm_le_one
        (norm_coordTruncation_apply_le _ _) (norm_nonneg _) zero_le_one))

theorem paperWoldCriticalCompositeCutoff_difference_norm_le_one (N : ℕ) :
    ‖paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N‖ ≤ 1 := by
  let m : PaperWoldMask := fun q => if q.1 < N ∧ q.2 < N then ⟨0, by simp⟩ else ⟨1, by simp⟩
  have he : paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N =
      (paperWoldCriticalCompositeKernel.mask m).toOperator := by
    apply HasLpMatrix.ext (K := fun n j => if n < N ∧ j < N then 0 else paperWoldCompositeEntry (1 / 2) n j)
    · intro n j
      change (paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N)
        (lp.single 2 j (1 : ℂ)) n = _
      simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, paperWoldCriticalCompositeOperator_single,
        paperWoldCriticalCompositeCutoff_single]
      split_ifs <;> simp
    · intro n j
      change (paperWoldCriticalCompositeKernel.mask m).toOperator (lp.single 2 j (1 : ℂ)) n = _
      rw [PaperHardy.Kernel.toOperator_single]
      change (m (n, j) : ℂ) * paperWoldCompositeEntry (1 / 2) n j = _
      by_cases h : n < N ∧ j < N <;> simp [m, h]
  rw [he]
  exact PaperHardy.Kernel.mask_norm_toOperator_le_one _ _ paperWoldCompositeEntry_critical_sharp_bound

theorem paperWoldCriticalCompositeCutoff_difference_compactIdealDistance (N : ℕ) :
    compactIdealDistance (paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N) = 1 := by
  rw [paperCompactIdealDistance_sub_compact paperWoldCriticalCompositeOperator
    ⟨_, paperWoldCriticalCompositeCutoff_compact N⟩, paperWoldCriticalCompositeOperator_compactIdealDistance]

theorem paperWoldCriticalCompositeCutoff_difference_norm (N : ℕ) :
    ‖paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N‖ = 1 := by
  apply le_antisymm (paperWoldCriticalCompositeCutoff_difference_norm_le_one N)
  simpa only [sub_zero, paperWoldCriticalCompositeCutoff_difference_compactIdealDistance] using
    compactIdealDistance_le (paperWoldCriticalCompositeOperator - paperWoldCriticalCompositeCutoff N)
      0 isCompactOperator_zero

theorem paperWoldCriticalCompositeCutoff_norm_tendsto_one :
    Tendsto (fun N => ‖paperWoldCriticalCompositeCutoff N‖) atTop (𝓝 1) := by
  rw [← paperWoldCriticalCompositeOperator_norm]
  apply tendsto_norm_of_strong_tendsto_of_norm_le paperWoldCriticalCompositeCutoff
    paperWoldCriticalCompositeOperator
  · intro N
    rw [paperWoldCriticalCompositeOperator_norm]
    exact paperWoldCriticalCompositeCutoff_norm_le_one N
  · exact paperWoldCriticalCompositeCutoff_strong_tendsto

end
end RHTower
