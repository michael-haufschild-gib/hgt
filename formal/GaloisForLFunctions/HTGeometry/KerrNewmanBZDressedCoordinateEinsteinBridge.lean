import GaloisForLFunctions.HTGeometry.CoordinateCurvature
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovSmoothMetricBridge

/-!
# Vacuum coordinate Einstein equation for the flat BZ-dressed Kerr--Newman lift

The full four-dimensional BZ lift is a constant metric congruent to Minkowski space.  Using the
coordinate-curvature layer, all Christoffel symbols, curvature contractions, and the coordinate
Einstein tensor vanish identically.  This is a closed vacuum Einstein equation for that concrete
flat lift.

It is not an Einstein--Maxwell calculation for the curved Kerr--Newman metric.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators ContDiff

/-- The constant flat BZ lift has zero coordinate Christoffel symbols. -/
theorem kerrNewmanFlatBZDressed_coordinateChristoffel_zero
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    coordinateChristoffel (kerrNewmanFlatBZDressedSmoothMetric parameter) x = 0 := by
  ext upper lower₁ lower₂
  simp [coordinateChristoffel, kerrNewmanFlatBZDressedSmoothMetric,
    coordPartial_const]

/-- The constant flat BZ lift has zero coordinate Riemann tensor. -/
theorem kerrNewmanFlatBZDressed_coordinateRiemann_zero
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    (fun upper lower deriv₁ deriv₂ =>
      coordinateRiemann (kerrNewmanFlatBZDressedSmoothMetric parameter) x
        upper lower deriv₁ deriv₂) = 0 := by
  funext upper lower deriv₁ deriv₂
  simp [coordinateRiemann, kerrNewmanFlatBZDressed_coordinateChristoffel_zero,
    coordPartial_const]

/-- The flat BZ lift has zero coordinate Ricci tensor. -/
theorem kerrNewmanFlatBZDressed_coordinateRicci_zero
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    coordinateRicci (kerrNewmanFlatBZDressedSmoothMetric parameter) x = 0 := by
  ext lower₁ lower₂
  simp [coordinateRicci, kerrNewmanFlatBZDressed_coordinateRiemann_zero]

/-- The flat BZ lift has zero coordinate scalar curvature. -/
theorem kerrNewmanFlatBZDressed_coordinateScalarCurvature_zero
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    coordinateScalarCurvature (kerrNewmanFlatBZDressedSmoothMetric parameter) x = 0 := by
  simp [coordinateScalarCurvature, kerrNewmanFlatBZDressed_coordinateRicci_zero]

/-- The flat BZ lift satisfies the vacuum coordinate Einstein equation. -/
theorem kerrNewmanFlatBZDressed_coordinateEinsteinTensor_zero
    (parameter : ℝ) (x : Fin 4 → ℝ) :
    coordinateEinsteinTensor (kerrNewmanFlatBZDressedSmoothMetric parameter) x = 0 := by
  ext lower₁ lower₂
  unfold coordinateEinsteinTensor
  rw [kerrNewmanFlatBZDressed_coordinateRicci_zero,
    kerrNewmanFlatBZDressed_coordinateScalarCurvature_zero]
  simp

end GaloisForLFunctions.HTGeometry
