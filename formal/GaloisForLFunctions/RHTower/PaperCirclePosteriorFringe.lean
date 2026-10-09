import GaloisForLFunctions.RHTower.PaperCircleCellPosterior
import GaloisForLFunctions.HTGeometry.PaperFourierLLogL.Edges.Fringe

/-! # Boundary-strip control after native observations

The source's thin-strip estimate transfers from uniform cell mass to the actual
conditional posterior. The history's paid evidence bound makes the estimate explicit.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic.Procedure

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- The grid is chosen deep enough to resolve every strip and the posterior comparison scale. -/
theorem paperCircleHistoryCellPosterior_fringe (a : ι → CCMCircleBoundedSymbol)
    (l r k j : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    (paperCircleHistoryCellPosterior a l (reach j+r) k i s).prob
      (flanked (paperCircleObservationCell l i) j) ≤
        4 * Period.side (reach j) * (paperCircleObservationCell l i).len /
          paperCircleHistoryCellEvidence a l (reach j+r) k i s := by
  have hc := paperCircleHistoryCellEvidence_pos a l (reach j+r) k i s
  have h := flank_prob (M:=l+(reach j+r)+10) (paperCircleObservationCell l i) i.isLt j
    (by unfold lanes paperCircleObservationCell; dsimp; omega)
  apply (paperCircleHistoryCellPosterior_prob_le a l (reach j+r) k i s _).trans
  calc
    _ ≤ ((paperCircleObservationCell l i).len /
        paperCircleHistoryCellEvidence a l (reach j+r) k i s) * (4 * Period.side (reach j)) :=
      mul_le_mul_of_nonneg_left h (div_pos (paperCircleObservationCell l i).len_pos hc).le
    _ = _ := by ring

/-- No unknown denominator remains: actual history energy and comparison free energy pay the cost. -/
theorem paperCircleHistoryCellPosterior_fringe_exp (a : ι → CCMCircleBoundedSymbol)
    (l r k j : ℕ) (i : Fin (2^l)) (s : List (ℝ≥0 × Grid (l+(reach j+r)+10))) :
    (paperCircleHistoryCellPosterior a l (reach j+r) k i s).prob
      (flanked (paperCircleObservationCell l i) j) ≤
        16 * Period.side (reach j) * (paperCircleObservationCell l i).len *
          Real.exp (2 * Thermal.sumE (paperCircleObservationProfile a (l+(reach j+r)+10) k s)
            ((paperCircleObservationCell l i).start (l+(reach j+r)+10)) +
              Thermal.F (paperCircleHistoryComparisonForm a l (reach j+r) k i s)) := by
  apply (paperCircleHistoryCellPosterior_fringe a l r k j i s).trans
  let X := 2 * Thermal.sumE (paperCircleObservationProfile a (l+(reach j+r)+10) k s)
    ((paperCircleObservationCell l i).start (l+(reach j+r)+10)) +
      Thermal.F (paperCircleHistoryComparisonForm a l (reach j+r) k i s)
  let E := paperCircleHistoryCellEvidence a l (reach j+r) k i s
  have he : 0 < E := paperCircleHistoryCellEvidence_pos a l (reach j+r) k i s
  have hlow : Real.exp (-X)/4 ≤ E := by
    simpa only [X, neg_add_rev, add_comm, sub_eq_add_neg] using
      paperCircleHistoryCellEvidence_lower a l (reach j+r) k i s
  have h1 : 1 ≤ E * (4 * Real.exp X) := by
    calc
      1 = (Real.exp (-X)/4) * (4 * Real.exp X) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (by positivity)
  apply (div_le_iff₀ he).mpr
  have h2 := mul_le_mul_of_nonneg_left h1
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) (Period.side_pos (reach j)).le)
      (paperCircleObservationCell l i).len_pos.le)
  change 4 * Period.side (reach j) * (paperCircleObservationCell l i).len ≤
    16 * Period.side (reach j) * (paperCircleObservationCell l i).len * Real.exp X * E
  nlinarith

end
end RHTower
