import GaloisForLFunctions.RHTower.PaperHurwitzWallApproach
import GaloisForLFunctions.HTGeometry.CompactUniformStrong

/-! # Compact observations cannot retain the native Hurwitz wall gap

The original approaching resolvents stay one unit from the identity, but their
action after every fixed compact input converges to that input in operator norm.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped ENNReal

/-- Every fixed compact input erases the norm gap of the literal Hurwitz source approach. -/
theorem paperHurwitzApproachPoint_comp_compact_tendsto (t : ℝ)
    (K : compactOperatorStarAlgebra PaperHurwitzHistory) :
    Tendsto (fun N => paperHurwitzResolvent (paperHurwitzApproachPoint t N) ∘L K.val)
      atTop (𝓝 K.val) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_norm_comp_of_isCompactOperator
    (fun N => paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1)
    (fun N => (paperHurwitzApproachPoint_norm_gap t N).le)
    (fun f => by
      simpa only [sub_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, sub_self] using
        (tendsto_paperHurwitzApproachPoint_strong t f).sub (tendsto_const_nhds (x := f)))
    K.val K.property
  simpa only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using h

theorem paperHurwitzApproachPoint_comp_compact_traceCost (t : ℝ) (N : ℕ)
    (K : compactOperatorStarAlgebra PaperHurwitzHistory) :
    compactOperatorTraceCost PaperHurwitzHistory
      (paperHurwitzResolvent (paperHurwitzApproachPoint t N) ∘L K.val) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr
    (K.property.clm_comp (paperHurwitzResolvent (paperHurwitzApproachPoint t N)))

end
end RHTower
