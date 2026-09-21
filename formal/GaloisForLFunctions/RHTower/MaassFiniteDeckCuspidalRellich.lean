import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGridBudget
import GaloisForLFunctions.HTGeometry.FiniteApproxTotallyBounded
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Rellich compactness for the completed cuspidal finite-deck form

Finite reciprocal grids approximate the entire completed cuspidal form unit
ball.  Their finite-dimensionality makes the first-coordinate inclusion a
compact operator.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The `L²` image of the completed cuspidal form unit ball is totally bounded. -/
theorem totallyBounded_cuspidalFormInclusion_closedBall (N : ℕ) :
    TotallyBounded (cuspidalFormInclusion N ''
      Metric.closedBall (0 : CuspidalFormDomain N) 1) := by
  apply totallyBounded_of_finiteDimensional_approx (M := 1)
  · rintro f ⟨v, hv, rfl⟩
    have hvnorm : ‖(v : FormTriple N)‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hv
      exact hv
    have hcoord := PiLp.norm_apply_le (v : FormTriple N) (0 : Fin 3)
    change ‖cuspidalFormInclusion N v‖ ≤ ‖(v : FormTriple N)‖ at hcoord
    exact hcoord.trans hvnorm
  · intro ε hε
    obtain ⟨M, K, hM, hY, hbudget⟩ := exists_reciprocal_grid_budget_lt N hε
    let W : Submodule ℂ (DeckL2 N) :=
      deckFiniteCellSpan (N := N)
        (upperChartGridCell (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
        (measurableSet_upperChartGridCell (M := M) (K := K)
          (-(1 : ℝ) / 2) (Real.sqrt 3 / 2) ((M : ℝ)⁻¹) ((M : ℝ)⁻¹))
    let V : Submodule ℝ (DeckL2 N) := W.restrictScalars ℝ
    refine ⟨V, ?_, ?_⟩
    · have hW : FiniteDimensional ℂ W := by
        dsimp [W]
        exact finiteDimensional_deckFiniteCellSpan _ _
      letI : FiniteDimensional ℂ W := hW
      change FiniteDimensional ℝ W
      exact FiniteDimensional.trans ℝ ℂ W
    · rintro f ⟨v, hv, rfl⟩
      have hvnorm : ‖(v : FormTriple N)‖ ≤ 1 := by
        rw [Metric.mem_closedBall, dist_zero_right] at hv
        exact hv
      obtain ⟨g, hg, hgdist⟩ :=
        exists_reciprocal_grid_cuspidal_witness_of_formNorm_le_one hM hY hbudget v hvnorm
      refine ⟨g, ?_, hgdist.le⟩
      change g ∈ W.restrictScalars ℝ
      rw [Submodule.restrictScalars_mem]
      simpa [W] using hg

/-- The first-coordinate inclusion of the completed cuspidal finite-deck form
is compact. -/
theorem isCompactOperator_cuspidalFormInclusion (N : ℕ) :
    IsCompactOperator (cuspidalFormInclusion N) := by
  refine ⟨closure (cuspidalFormInclusion N ''
      Metric.closedBall (0 : CuspidalFormDomain N) 1), ?_, ?_⟩
  · exact (totallyBounded_cuspidalFormInclusion_closedBall N).closure.isCompact_of_isClosed
      isClosed_closure
  · apply Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : CuspidalFormDomain N) zero_lt_one)
    intro v hv
    change cuspidalFormInclusion N v ∈ closure (cuspidalFormInclusion N ''
      Metric.closedBall (0 : CuspidalFormDomain N) 1)
    apply subset_closure
    exact ⟨v, Metric.mem_closedBall.mpr (Metric.mem_ball.mp hv).le, rfl⟩

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
