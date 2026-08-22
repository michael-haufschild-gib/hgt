import GaloisForLFunctions.HTGeometry.EulerRieszDilationInstability
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticCloud

/-!
# Euler--Riesz profile inside the Bourgain square-root curve

The two nonconstant homogeneous terms of the normalized Euler--Riesz dilation profile are exactly
the quadratic and three-halves coordinates of the Bourgain square-root curve.  Thus its stationary
scale direction has a literal phase-space realization.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The Bourgain phase-space vector realizing the normalized Euler--Riesz dilation profile. -/
noncomputable def eulerRieszBourgainPhase (amplitude : ℝ) : BourgainPhaseSpace :=
  ![0, -(3 / 2 : ℝ) * (amplitude ^ 2 + 1), 2 * (amplitude ^ 2 + 1), 0]

/-- The Euler--Riesz dilation profile is a square-root-curve phase, up to its invariant mass term. -/
theorem eulerRieszDilationProfile_eq_bourgainSquareRootCurvePhase
    (amplitude massOffset scale : ℝ) :
    eulerRieszDilationProfile amplitude massOffset scale =
      bourgainSquareRootCurvePhase (eulerRieszBourgainPhase amplitude) scale + massOffset := by
  rw [bourgainSquareRootCurvePhase_eq]
  simp [eulerRieszDilationProfile, eulerRieszBourgainPhase]
  ring

/-- The Euler--Riesz phase has zero square-root-curve linear coordinate at unit scale. -/
theorem eulerRieszBourgainPhase_linear_unit (amplitude : ℝ) :
    bourgainSquareRootLinearPhaseCoordinate 1 (eulerRieszBourgainPhase amplitude) = 0 := by
  simp [bourgainSquareRootLinearPhaseCoordinate, eulerRieszBourgainPhase]
  ring

/-- The Euler--Riesz phase has negative square-root-curve quadratic coordinate at unit scale. -/
theorem eulerRieszBourgainPhase_quadratic_unit (amplitude : ℝ) :
    bourgainSquareRootQuadraticPhaseCoordinate 1 (eulerRieszBourgainPhase amplitude)
      = -(3 / 4 : ℝ) * (amplitude ^ 2 + 1) := by
  simp [bourgainSquareRootQuadraticPhaseCoordinate, eulerRieszBourgainPhase]
  ring

/-- The Euler--Riesz phase curves strictly downward in the unit-scale Bourgain coordinate. -/
theorem eulerRieszBourgainPhase_quadratic_unit_neg (amplitude : ℝ) :
    bourgainSquareRootQuadraticPhaseCoordinate 1 (eulerRieszBourgainPhase amplitude) < 0 := by
  rw [eulerRieszBourgainPhase_quadratic_unit]
  have hpos : 0 < amplitude ^ 2 + 1 := by positivity
  nlinarith

/-- The Euler--Riesz phase is orthogonal to the unit-scale linear jet of the quadratic cloud. -/
theorem bourgainDot_eulerRieszBourgainPhase_linearJet_unit (amplitude : ℝ) :
    bourgainDot (eulerRieszBourgainPhase amplitude) (bourgainSquareRootLinearJet 1) = 0 := by
  simp [bourgainDot, eulerRieszBourgainPhase, bourgainSquareRootLinearJet, Fin.sum_univ_four]
  ring

/-- Pairing the Euler--Riesz phase with the unit-scale quadratic jet gives its curvature. -/
theorem bourgainDot_eulerRieszBourgainPhase_quadraticJet_unit (amplitude : ℝ) :
    bourgainDot (eulerRieszBourgainPhase amplitude) (bourgainSquareRootQuadraticJet 1)
      = -(3 / 4 : ℝ) * (amplitude ^ 2 + 1) := by
  simp [bourgainDot, eulerRieszBourgainPhase, bourgainSquareRootQuadraticJet, Fin.sum_univ_four]
  ring

end RHTower
