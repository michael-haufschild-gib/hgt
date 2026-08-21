import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Thickening
open MeasureTheory Metric Set

-- compact inside open gives a thickening
example (s t : Set (Fin 3 → ℝ)) (hs : IsCompact s) (ht : IsOpen t) (hst : s ⊆ t) :
    ∃ δ > 0, thickening δ s ⊆ t := hs.exists_thickening_subset_open ht hst

-- ball inside thickening of closedBall
example (x : Fin 3 → ℝ) (R δ : ℝ) (hR : 0 < R) (hδ : 0 < δ) :
    ball x (R + δ) ⊆ thickening δ (closedBall x R) := by
  exact?

