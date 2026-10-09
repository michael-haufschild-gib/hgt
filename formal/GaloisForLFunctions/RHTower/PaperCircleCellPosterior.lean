import GaloisForLFunctions.RHTower.PaperCirclePosteriorEvidence

/-! # Native history posteriors conditioned on dyadic cells

Every cell has positive evidence. Conditioning therefore uses the genuine conditional
law, and its density relative to the uniform cell law has an explicit upper bound.
-/

open scoped BigOperators NNReal Classical
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

def paperCircleHistoryCellPosterior (a : ι → CCMCircleBoundedSymbol) (l r k : ℕ)
    (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) : Law (Grid (l+r+10)) :=
  (paperCircleHistoryPosterior a (l+r+10) k s).condP
    (fun x => x ∈ (paperCircleObservationCell l i).block (l+r+10))

theorem paperCircleHistoryCellPosterior_apply (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (x : Grid (l+r+10)) :
    paperCircleHistoryCellPosterior a l r k i s x =
      if x ∈ (paperCircleObservationCell l i).block (l+r+10) then
        Period.side (l+r+10) * paperCircleHistoryLikelihood a (l+r+10) k s x /
          paperCircleHistoryCellEvidence a l r k i s else 0 := by
  rw [paperCircleHistoryCellPosterior, Law.condP_pos_apply _ _
    (paperCircleHistoryPosterior_cell_pos a l r k i s), paperCircleHistoryPosterior_cell]
  split_ifs
  · rw [paperCircleHistoryPosterior_apply]
    field_simp [(paperCircleHistoryEvidence_pos a (l+r+10) k s).ne']
  · simp

theorem paperCircleHistoryCellPosterior_pos_iff (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (x : Grid (l+r+10)) :
    0 < paperCircleHistoryCellPosterior a l r k i s x ↔
      x ∈ (paperCircleObservationCell l i).block (l+r+10) := by
  rw [paperCircleHistoryCellPosterior, Law.condP_mem (paperCircleHistoryPosterior_cell_pos a l r k i s)]
  simp only [paperCircleHistoryPosterior_pos, and_true]

/-- Exact density relative to the uniform law on the cell. -/
theorem paperCircleHistoryCellPosterior_density (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (x : Grid (l+r+10)) :
    paperCircleHistoryCellPosterior a l r k i s x =
      ((paperCircleObservationCell l i).len / paperCircleHistoryCellEvidence a l r k i s) *
        (paperCircleObservationCell l i).dice (l+r+10) x *
          paperCircleHistoryLikelihood a (l+r+10) k s x := by
  rw [paperCircleHistoryCellPosterior_apply, Node.dice_apply (paperCircleObservationCell_ok l r i)]
  split_ifs
  · field_simp [(paperCircleObservationCell l i).len_pos.ne']
  · simp

theorem paperCircleHistoryCellPosterior_density_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (x : Grid (l+r+10)) :
    paperCircleHistoryCellPosterior a l r k i s x ≤
      ((paperCircleObservationCell l i).len / paperCircleHistoryCellEvidence a l r k i s) *
        (paperCircleObservationCell l i).dice (l+r+10) x := by
  rw [paperCircleHistoryCellPosterior_density]
  exact mul_le_of_le_one_right
    (mul_nonneg (div_pos (paperCircleObservationCell l i).len_pos
      (paperCircleHistoryCellEvidence_pos a l r k i s)).le (Law.nonneg _ _))
    (paperCircleHistoryLikelihood_le_one a (l+r+10) k s x)

/-- Any uniform-cell event bound transfers to the actual conditioned history. -/
theorem paperCircleHistoryCellPosterior_prob_le (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (event : Grid (l+r+10) → Prop) :
    (paperCircleHistoryCellPosterior a l r k i s).prob event ≤
      ((paperCircleObservationCell l i).len / paperCircleHistoryCellEvidence a l r k i s) *
        ((paperCircleObservationCell l i).dice (l+r+10)).prob event := by
  rw [Law.prob_eq, Law.prob_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact paperCircleHistoryCellPosterior_density_le a l r k i s x
  · simp

theorem paperCircleHistoryCellPosterior_abs_expectation (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10)))
    (f : Grid (l+r+10) → ℝ) :
    (paperCircleHistoryCellPosterior a l r k i s).Ex (fun x => |f x|) ≤
      ((paperCircleObservationCell l i).len / paperCircleHistoryCellEvidence a l r k i s) *
        (paperCircleObservationCell l i).avg (fun x => |f x|) := by
  rw [Node.avg_ex (paperCircleObservationCell_ok l r i)]
  simp only [Law.Ex, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_right (paperCircleHistoryCellPosterior_density_le a l r k i s x) (abs_nonneg _)

/-- The normalization used by the source's cell actor is exactly the native cell evidence. -/
theorem paperCircleHistoryCellEvidence_avg (a : ι → CCMCircleBoundedSymbol)
    (l r k : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+r+10))) :
    (paperCircleObservationCell l i).avg (paperCircleHistoryLikelihood a (l+r+10) k s) =
      paperCircleHistoryCellEvidence a l r k i s / (paperCircleObservationCell l i).len := by
  have hi : ((paperCircleObservationCell l i).block (l+r+10)).indicator
      (paperCircleHistoryLikelihood a (l+r+10) k s) =
        Thermal.prefixE (paperCircleObservationProfile a (l+r+10) k s)
          (paperCircleObservationCell l i) := by
    funext x
    simp [Set.indicator, paperCircleHistoryLikelihood, Thermal.prefixE]
  rw [Node.avg, hi]
  change (paperCircleObservationCell l i).len⁻¹ *
      expU (Thermal.prefixE (paperCircleObservationProfile a (l+r+10) k s)
        (paperCircleObservationCell l i)) =
    paperCircleHistoryCellEvidence a l r k i s / (paperCircleObservationCell l i).len
  unfold paperCircleHistoryCellEvidence
  ring

end
end RHTower
