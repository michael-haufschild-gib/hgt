import GaloisForLFunctions.RHTower.PaperWoldCompositeDamping

/-! # Exact parameter transport of the complete composite matrix

Changing the exponent is exactly left composition by the native row-damping
semigroup. The full family is strongly continuous, but the compactness boundary
retains the critical operator's entire distance from the compact ideal.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

def paperWoldCompositeDampingTime (t : {t : ℝ // t ≤ 1 / 2}) : ℝ≥0 :=
  ⟨1 - 2 * (t : ℝ), by linarith [t.property]⟩

theorem paperWoldCompositeDampingTime_coe (t : {t : ℝ // t ≤ 1 / 2}) :
    (paperWoldCompositeDampingTime t : ℝ) = 1 - 2 * (t : ℝ) := rfl

theorem paperWoldCompositeEntry_row_factor (t : {t : ℝ // t ≤ 1 / 2}) (n j : ℕ) :
    paperWoldCompositeEntry t n j =
      (paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n : ℂ) *
        paperWoldCompositeEntry (1 / 2) n j := by
  rw [paperWoldCompositeEntry_formula, paperWoldCompositeEntry_critical_formula]
  by_cases h : n < j
  · rw [if_pos h, if_pos h]
    have hp : (2 * (n : ℝ) + 3) ^ (2 * (t : ℝ)) =
        paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n * (2 * n + 3) := by
      change (2 * (n : ℝ) + 3) ^ (2 * (t : ℝ)) =
        (2 * (n : ℝ) + 3) ^ (-(paperWoldCompositeDampingTime t : ℝ)) * (2 * n + 3)
      have he : -(paperWoldCompositeDampingTime t : ℝ) + 1 = 2 * (t : ℝ) := by
        rw [paperWoldCompositeDampingTime_coe]
        ring
      simpa only [he, Real.rpow_one] using
        Real.rpow_add (by positivity : 0 < 2 * (n : ℝ) + 3) (-(paperWoldCompositeDampingTime t : ℝ)) 1
    rw [hp]
    push_cast
    ring
  · rw [if_neg h, if_neg h, mul_zero]

/-- Every original coefficient survives in this exact complete-operator factorization. -/
theorem paperWoldCompositeOperator_factor (t : {t : ℝ // t ≤ 1 / 2}) :
    paperWoldCompositeOperator t =
      paperWoldCompositeDamping (paperWoldCompositeDampingTime t) ∘L paperWoldCriticalCompositeOperator := by
  apply HasLpMatrix.ext (paperWoldCompositeOperator_matrix t)
  intro n j
  simp only [ContinuousLinearMap.comp_apply, paperWoldCompositeDamping_apply, lpBasisVec,
    paperWoldCriticalCompositeOperator_single]
  exact (paperWoldCompositeEntry_row_factor t n j).symm

theorem paperWoldCompositeOperator_row (t : {t : ℝ // t ≤ 1 / 2})
    (f : PaperWoldHistory) (n : ℕ) :
    paperWoldCompositeOperator t f n =
      (paperWoldCompositeDampingWeight (paperWoldCompositeDampingTime t) n : ℂ) *
        paperWoldCriticalCompositeOperator f n := by
  rw [paperWoldCompositeOperator_factor, ContinuousLinearMap.comp_apply, paperWoldCompositeDamping_apply]

theorem paperWoldCompositeDampingTime_continuous : Continuous paperWoldCompositeDampingTime :=
  (continuous_const.sub (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The literal exponent family is strongly continuous throughout its entire admitted domain. -/
theorem paperWoldCompositeOperator_strong_continuous (f : PaperWoldHistory) :
    Continuous (fun t : {t : ℝ // t ≤ 1 / 2} => paperWoldCompositeOperator t f) := by
  simp_rw [paperWoldCompositeOperator_factor, ContinuousLinearMap.comp_apply]
  exact (paperWoldCompositeDamping_strong_continuous (paperWoldCriticalCompositeOperator f)).comp
    paperWoldCompositeDampingTime_continuous

/-- The native row scale sharpens the previously uniform complete-family norm budget. -/
theorem paperWoldCompositeOperator_scaled_norm_le (t : {t : ℝ // t ≤ 1 / 2}) :
    ‖paperWoldCompositeOperator t‖ ≤ 5 * (3 : ℝ) ^ (2 * (t : ℝ) - 1) := by
  rw [paperWoldCompositeOperator_factor]
  have h := ((paperWoldCompositeDamping (paperWoldCompositeDampingTime t)).opNorm_comp_le
    paperWoldCriticalCompositeOperator).trans
    (mul_le_mul_of_nonneg_left paperWoldCriticalCompositeOperator_norm_le (norm_nonneg _))
  rw [paperWoldCompositeDamping_norm, paperWoldCompositeDampingTime_coe,
    show -(1 - 2 * (t : ℝ)) = 2 * t - 1 by ring] at h
  simpa only [mul_comm] using h

/-- Every strict-half member stays a fixed norm distance from the complete endpoint operator. -/
theorem paperWoldCompositeOperator_critical_norm_gap (t : {t : ℝ // t < 1 / 2}) :
    (1 / 24 : ℝ) ≤ ‖paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩‖ :=
  paperWoldCriticalCompositeOperator_norm_sub_compact_floor
    ⟨_, paperWoldCompositeOperator_compact t⟩

theorem paperWoldCompositeOperator_critical_compactIdealDistance
    (t : {t : ℝ // t < 1 / 2}) :
    compactIdealDistance (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩) =
      compactIdealDistance paperWoldCriticalCompositeOperator :=
  paperCompactIdealDistance_sub_compact paperWoldCriticalCompositeOperator
    ⟨_, paperWoldCompositeOperator_compact t⟩

theorem paperWoldCompositeOperator_critical_difference_traceCost
    (t : {t : ℝ // t < 1 / 2}) :
    compactOperatorTraceCost PaperWoldHistory
      (paperWoldCriticalCompositeOperator - paperWoldCompositeOperator ⟨t, t.property.le⟩) = ∞ := by
  have h := compactOperatorTraceCost_add_compact paperWoldCriticalCompositeOperator
    (⟨-paperWoldCompositeOperator ⟨t, t.property.le⟩, (paperWoldCompositeOperator_compact t).neg⟩ :
      compactOperatorStarAlgebra PaperWoldHistory)
  simpa only [sub_eq_add_neg, paperWoldCriticalCompositeOperator_traceCost] using h

end
end RHTower
