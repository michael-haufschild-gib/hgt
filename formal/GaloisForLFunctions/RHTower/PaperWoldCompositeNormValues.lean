import GaloisForLFunctions.RHTower.PaperWoldCompositeNormContinuity

/-! # Continuous norm values despite the critical operator-norm gap

The complete family has continuous scalar norm on its entire closed-half
domain. In particular, its norm values converge along the literal exponent
approach even though the operators fail to converge in operator norm.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

theorem paperWoldCompositeOperator_norm_le_critical (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCompositeOperator t‖ ≤ ‖paperWoldCriticalCompositeOperator‖ := by
  have hd : ‖paperWoldCompositeDamping (paperWoldCompositeDampingTime t)‖ ≤ 1 :=
    norm_lpDiagonalCLM_le _ _ _
  rw [paperWoldCompositeOperator_factor]
  exact ((paperWoldCompositeDamping _).opNorm_comp_le _).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hd (norm_nonneg paperWoldCriticalCompositeOperator))

/-- Scalar operator norms stay continuous even where the operator-valued map is discontinuous. -/
theorem paperWoldCompositeOperator_norm_continuous :
    Continuous (fun t : {t : ℝ // t ≤ 1 / 2} => ‖paperWoldCompositeOperator t‖) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : (t : ℝ) < 1 / 2
  · exact ((paperWoldCompositeOperator_continuousAt_iff t).mpr ht).norm
  · have he : t = ⟨1 / 2, le_rfl⟩ :=
      Subtype.ext (le_antisymm t.property (le_of_not_gt ht))
    subst t
    change Tendsto (fun u => ‖paperWoldCompositeOperator u‖) (𝓝 ⟨1 / 2, le_rfl⟩)
      (𝓝 ‖paperWoldCompositeOperator ⟨1 / 2, le_rfl⟩‖)
    rw [paperWoldCompositeOperator_critical]
    apply tendsto_norm_of_strong_tendsto_of_norm_le paperWoldCompositeOperator
      paperWoldCriticalCompositeOperator paperWoldCompositeOperator_norm_le_critical
    intro f
    simpa only [paperWoldCompositeOperator_critical] using
      (paperWoldCompositeOperator_strong_continuous f).tendsto ⟨1 / 2, le_rfl⟩

theorem paperWoldCompositeApproach_norm_tendsto :
    Tendsto (fun N => ‖paperWoldCompositeApproach N‖) atTop
      (𝓝 ‖paperWoldCriticalCompositeOperator‖) := by
  have h := (paperWoldCompositeOperator_norm_continuous.tendsto ⟨1 / 2, le_rfl⟩).comp
    paperWoldCompositeApproachParameter_tendsto
  simpa only [Function.comp_def, paperWoldCompositeApproach, paperWoldCompositeOperator_critical] using h

end
end RHTower
