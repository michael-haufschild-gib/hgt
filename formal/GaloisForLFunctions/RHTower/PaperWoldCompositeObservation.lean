import GaloisForLFunctions.RHTower.PaperWoldCompositeApproach
import GaloisForLFunctions.HTGeometry.CompactUniformStrong

/-! # Compact observations of the literal composite exponent family

The raw critical norm gap becomes invisible after every fixed compact input
observation. This holds for full compact operators, not only finite matrices.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

theorem paperWoldCompositeDamping_sub_norm_le (r s : ℝ≥0) :
    ‖paperWoldCompositeDamping r - paperWoldCompositeDamping s‖ ≤ 1 := by
  have hb (n : ℕ) :
      ‖(paperWoldCompositeDampingWeight r n : ℂ) - (paperWoldCompositeDampingWeight s n : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [paperWoldCompositeDampingWeight_pos r n, paperWoldCompositeDampingWeight_le_one s n]
    · linarith [paperWoldCompositeDampingWeight_le_one r n, paperWoldCompositeDampingWeight_pos s n]
  have he : paperWoldCompositeDamping r - paperWoldCompositeDamping s =
      lpDiagonalCLM (fun n => (paperWoldCompositeDampingWeight r n : ℂ) -
        (paperWoldCompositeDampingWeight s n : ℂ)) zero_le_one hb := by
    ext f n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, paperWoldCompositeDamping_apply,
      lpDiagonalCLM_apply, sub_mul]
  rw [he]
  exact norm_lpDiagonalCLM_le _ _ _

theorem paperWoldCompositeDamping_comp_compact_continuous
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Continuous (fun r : ℝ≥0 => paperWoldCompositeDamping r ∘L K.val) := by
  rw [continuous_iff_continuousAt]
  intro s
  change Tendsto (fun r => paperWoldCompositeDamping r ∘L K.val) (𝓝 s)
    (𝓝 (paperWoldCompositeDamping s ∘L K.val))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_norm_comp_of_isCompactOperator
    (fun r => paperWoldCompositeDamping r - paperWoldCompositeDamping s)
    (fun r => paperWoldCompositeDamping_sub_norm_le r s)
    (fun f => by
      simpa only [sub_apply, sub_self] using
        ((paperWoldCompositeDamping_strong_continuous f).tendsto s).sub
          (tendsto_const_nhds (x := paperWoldCompositeDamping s f))) K.val K.property
  simpa only [ContinuousLinearMap.sub_comp] using h

/-- Every fixed compact input observation sees norm continuity even at the critical exponent. -/
theorem paperWoldCompositeOperator_comp_compact_continuous
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Continuous (fun t : {t : ℝ // t ≤ 1 / 2} => paperWoldCompositeOperator t ∘L K.val) := by
  have h := (paperWoldCompositeDamping_comp_compact_continuous
    ⟨paperWoldCriticalCompositeOperator ∘L K.val,
      K.property.clm_comp paperWoldCriticalCompositeOperator⟩).comp
      paperWoldCompositeDampingTime_continuous
  simpa only [Function.comp_def, paperWoldCompositeOperator_factor,
    ContinuousLinearMap.comp_assoc] using h

theorem paperWoldCompositeOperator_comp_compact_traceCost
    (t : {t : ℝ // t ≤ 1 / 2}) (K : compactOperatorStarAlgebra PaperWoldHistory) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldCompositeOperator t ∘L K.val) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (K.property.clm_comp (paperWoldCompositeOperator t))

/-- The same exponent sequence with a raw norm gap converges in norm after every compact input. -/
theorem paperWoldCompositeApproach_comp_compact_tendsto
    (K : compactOperatorStarAlgebra PaperWoldHistory) :
    Tendsto (fun N => paperWoldCompositeApproach N ∘L K.val) atTop
      (𝓝 (paperWoldCriticalCompositeOperator ∘L K.val)) := by
  have h := ((paperWoldCompositeOperator_comp_compact_continuous K).tendsto ⟨1 / 2, le_rfl⟩).comp
    paperWoldCompositeApproachParameter_tendsto
  simpa only [Function.comp_def, paperWoldCompositeApproach, paperWoldCompositeOperator_critical] using h

end
end RHTower
