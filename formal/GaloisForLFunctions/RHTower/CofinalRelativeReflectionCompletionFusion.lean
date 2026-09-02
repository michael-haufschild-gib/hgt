import GaloisForLFunctions.RHTower.IntegralRelativeReflectionComplexFusion
import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology

/-!
# Cofinal relative-reflection completion fusion

The universal integral relative-reflection matrix is not merely a static Laurent object. At every
finite Tate stage its two physical arrows are recovered exactly by reading the newly created top
coordinate of the flat-minus-scaled cofinal naturality defects at reciprocal Gamma clocks.

Consequently the source Clifford square and determinant are literal completion anomalies. This
is unconditional and does not assert the remaining integral strictness of the completed Xi
realization.
-/

open Complex Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical reader of the new top coordinate born at one Tate stage. -/
def tateClockCofinalTopCoefficient
    (m : ℕ) (v : Fin (m + 2) → ℂ) : ℂ :=
  v (Fin.last (m + 1))

/-- Reciprocal flat-minus-scaled Tate anomalies, assembled as one rank-two odd matrix. -/
def tateClockRelativeReflectionCofinalCoefficientMatrix
    (a : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,
      -tateClockCofinalTopCoefficient m
        (tateClockFlatMinusRawCofinalDefect (Real.exp a : ℂ) m
          (tateClockFinIntervalBasis ℂ (Fin.last m)));
    -tateClockCofinalTopCoefficient m
        (tateClockFlatMinusRawCofinalDefect (Real.exp (-a) : ℂ) m
          (tateClockFinIntervalBasis ℂ (Fin.last m))),
      0]

/-- The forward Tate top anomaly recovers the forward Gamma suspension leg without loss. -/
theorem tateClockCofinalTopCoefficient_flatMinusRaw_exp
    (a : ℝ) (m : ℕ) :
    -tateClockCofinalTopCoefficient m
        (tateClockFlatMinusRawCofinalDefect (Real.exp a : ℂ) m
          (tateClockFinIntervalBasis ℂ (Fin.last m))) =
      (sourceHorizontalGammaSixUnitForwardBoundaryDefect a : ℂ) := by
  rw [tateClockFlatMinusRawCofinalDefect_eq_topBoundary,
    tateClockFinIntervalTopBoundary_basis_last]
  simp [tateClockCofinalTopCoefficient,
    tateClockFinIntervalBasis,
    sourceHorizontalGammaSixUnitForwardBoundaryDefect_eq]

/-- The reflected Tate top anomaly recovers the reciprocal Gamma suspension leg without loss. -/
theorem tateClockCofinalTopCoefficient_flatMinusRaw_exp_neg
    (a : ℝ) (m : ℕ) :
    -tateClockCofinalTopCoefficient m
        (tateClockFlatMinusRawCofinalDefect (Real.exp (-a) : ℂ) m
          (tateClockFinIntervalBasis ℂ (Fin.last m))) =
      (sourceHorizontalGammaSixUnitReflectedBoundaryDefect a : ℂ) := by
  rw [tateClockFlatMinusRawCofinalDefect_eq_topBoundary,
    tateClockFinIntervalTopBoundary_basis_last]
  simp [tateClockCofinalTopCoefficient,
    tateClockFinIntervalBasis,
    sourceHorizontalGammaSixUnitReflectedBoundaryDefect_eq]

/-- Completion reconstruction: reciprocal Tate naturality defects recover exactly the Gamma
curved suspension, hence transported reflection minus bare reflection. -/
theorem tateClockRelativeReflectionCofinalCoefficientMatrix_eq_curvedSuspension
    (a : ℝ) (m : ℕ) :
    tateClockRelativeReflectionCofinalCoefficientMatrix a m =
      sourceHorizontalGammaSixCurvedSuspension a := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [tateClockRelativeReflectionCofinalCoefficientMatrix,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg]
  · simpa [tateClockRelativeReflectionCofinalCoefficientMatrix,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg] using
        (tateClockCofinalTopCoefficient_flatMinusRaw_exp a m)
  · simpa [tateClockRelativeReflectionCofinalCoefficientMatrix,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg] using
        (tateClockCofinalTopCoefficient_flatMinusRaw_exp_neg a m)
  · simp [tateClockRelativeReflectionCofinalCoefficientMatrix,
      sourceHorizontalGammaSixCurvedSuspension,
      sourceHorizontalGammaSixForwardSuspensionLeg,
      sourceHorizontalGammaSixReflectedSuspensionLeg]

/-- Completion Clifford law: the paired naturality anomaly squares to scalar curvature. -/
theorem tateClockRelativeReflectionCofinalCoefficientMatrix_sq
    (a : ℝ) (m : ℕ) :
    tateClockRelativeReflectionCofinalCoefficientMatrix a m *
        tateClockRelativeReflectionCofinalCoefficientMatrix a m =
      -(sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [tateClockRelativeReflectionCofinalCoefficientMatrix_eq_curvedSuspension,
    sourceHorizontalGammaSixCurvedSuspension_sq]

/-- Determinant of the paired completion anomaly is the positive Gamma curvature. -/
theorem det_tateClockRelativeReflectionCofinalCoefficientMatrix
    (a : ℝ) (m : ℕ) :
    Matrix.det (tateClockRelativeReflectionCofinalCoefficientMatrix a m) =
      (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature a : ℂ) := by
  rw [tateClockRelativeReflectionCofinalCoefficientMatrix_eq_curvedSuspension]
  exact det_sourceHorizontalGammaSixCurvedSuspension a

/-- Full source/completion conservation identity: evaluated determinant of the integral Laurent
matrix equals determinant of the canonical paired Tate naturality anomaly at every stage. -/
theorem deningerIntegralRelativeReflection_determinant_eq_cofinalTate
    (a : ℝ) (m : ℕ) :
    deningerIntegralGammaEvaluationComplex a
        (Matrix.det deningerIntegralRelativeReflectionDifferential) =
      Matrix.det (tateClockRelativeReflectionCofinalCoefficientMatrix a m) := by
  rw [deningerIntegralRelativeReflection_determinant_evaluation,
    det_tateClockRelativeReflectionCofinalCoefficientMatrix]

end


end RHTower
