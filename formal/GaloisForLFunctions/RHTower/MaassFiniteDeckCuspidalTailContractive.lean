import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail

/-!
# Contractivity of the finite-deck cusp cutoff

The sharp cuspidal tail estimate can be compared to a completed form coordinate
because the height cutoff is an `L²` contraction.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet

open MaassCongruenceL2 SelbergMaassCongruenceTrace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Cusp-tail multiplication by an indicator has `L²` operator norm at most one. -/
theorem norm_cuspTailProjection_le {N : ℕ} (Y : ℝ) (u : DeckL2 N) :
    ‖cuspTailProjection N Y u‖ ≤ ‖u‖ := by
  have hop : ‖cuspTailProjection N Y‖ ≤ 1 := by
    exact MeasureTheory.norm_lpBoundedSmulCLM_le (p := 2) (μ := cellMeasure)
      (H := DeckSpace N) (measurable_cuspTailCutoff Y) (by positivity)
      (norm_cuspTailCutoff_le_one Y)
  have happ := ContinuousLinearMap.le_of_opNorm_le (cuspTailProjection N Y) hop u
  simpa using happ

end

end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
