import GaloisForLFunctions.RHTower.PaperAbelRoutePTail
import GaloisForLFunctions.HTGeometry.PaperHalfLineReferenceObservation

/-! # Reference observations distinguish the full Abel and Route-P tails

Bare norm profiles agree. Two fixed reference phases distinguish every actual
nonnegative source tail, even though all bounded-input reference discrepancies
decay exponentially and every finite-tail difference has infinite ideal cost.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry MeasureTheory Filter
open scoped Topology NNReal ENNReal
private abbrev PaperAbelReferenceSpace := Lp ℂ 2 halfLineMeasure

theorem paperAbelRouteP_same_bare_observations (T : ℝ) (x : PaperAbelReferenceSpace) :
    ‖paperAbelTailOperator T x‖ = ‖paperRoutePTailOperator T x‖ :=
  paperHalfLineCayley_same_norm _ _ T x

theorem paperAbelRouteP_reference_distinguishes (T : ℝ≥0) :
    ∃ x : PaperAbelReferenceSpace,
      operatorReferenceNorm (paperAbelTailOperator T) 1 x ≠
        operatorReferenceNorm (paperRoutePTailOperator T) 1 x ∨
      operatorReferenceNorm (paperAbelTailOperator T) Complex.I x ≠
        operatorReferenceNorm (paperRoutePTailOperator T) Complex.I x := by
  classical
  by_contra h
  push Not at h
  have he := (paperHalfLineCayley_reference_eq_iff_tail
    paperCompletedAbelSource paperRoutePSource T).mp ⟨fun x => (h x).1, fun x => (h x).2⟩
  have hp := (paperAbelRouteP_source_difference T).1
  rw [he T le_rfl, sub_self] at hp
  exact lt_irrefl _ hp

theorem paperAbelRouteP_reference_difference_le (T : ℝ≥0) (z : ℂ)
    (x : PaperAbelReferenceSpace) :
    |operatorReferenceNorm (paperAbelTailOperator T) z x -
      operatorReferenceNorm (paperRoutePTailOperator T) z x| ≤
        (40 / 3) * Real.exp (-(T : ℝ) / 2) * ‖x‖ :=
  (operatorReferenceNorm_difference_le _ _ z x).trans
    (mul_le_mul_of_nonneg_right (paperAbelRoutePTailDifference_norm_le T) (norm_nonneg x))

/-- References may move arbitrarily with the tail parameter. -/
theorem paperAbelRouteP_moving_reference_tendsto (z : ℝ → ℂ)
    (x : PaperAbelReferenceSpace) :
    Tendsto (fun T : ℝ => operatorReferenceNorm (paperAbelTailOperator T) (z T) x -
      operatorReferenceNorm (paperRoutePTailOperator T) (z T) x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (g := fun T : ℝ => ‖paperAbelRoutePTailDifference T‖ * ‖x‖)
    (fun _ => norm_nonneg _) (fun T => ?_) ?_
  · simpa only [norm_zero, zero_mul] using
      paperAbelRoutePTailDifference_tendsto_zero.norm.mul_const ‖x‖
  · rw [Real.norm_eq_abs]
    exact operatorReferenceNorm_difference_le _ _ (z T) x

theorem paperAbelRouteP_reference_distinction_cost (T : ℝ≥0) :
    (∀ x : PaperAbelReferenceSpace,
      ‖paperAbelTailOperator T x‖ = ‖paperRoutePTailOperator T x‖) ∧
      (∃ x : PaperAbelReferenceSpace,
        operatorReferenceNorm (paperAbelTailOperator T) 1 x ≠
          operatorReferenceNorm (paperRoutePTailOperator T) 1 x ∨
        operatorReferenceNorm (paperAbelTailOperator T) Complex.I x ≠
          operatorReferenceNorm (paperRoutePTailOperator T) Complex.I x) ∧
      compactOperatorTraceCost PaperAbelReferenceSpace (paperAbelRoutePTailDifference T) = ∞ :=
  ⟨paperAbelRouteP_same_bare_observations T, paperAbelRouteP_reference_distinguishes T,
    paperAbelRoutePTailDifference_traceCost T⟩

end
end RHTower
