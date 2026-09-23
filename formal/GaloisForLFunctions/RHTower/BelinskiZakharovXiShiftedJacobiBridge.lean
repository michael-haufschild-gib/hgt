import GaloisForLFunctions.RHTower.XiShiftedJacobiFrameToda
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Belinski--Zakharov residues in the shifted Xi Jacobi flow

The finite shifted half-density Jacobi frame carries a Riccati flow with a terminal rank-one
boundary defect.  At its first nontrivial finite level, that defect is exactly the `2 × 2`
column--row residue used by the BZ layer.  This is an algebraic dictionary between a finite
admission boundary channel and a BZ residue; it asserts no relation to RH or to a spacetime
inverse-scattering solution.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open scoped Matrix

/-- The terminal boundary vector at the two-mode shifted Jacobi level. -/
theorem xiShiftedJacobi_boundaryUnit_one :
    ShiftedJacobiFrame.boundaryUnit 1 = ![0, 1] := by
  funext i
  fin_cases i <;>
    simp [ShiftedJacobiFrame.boundaryUnit]

/-- The two-mode Jacobi boundary source is precisely a BZ rank-one residue. -/
theorem xiShiftedJacobi_boundarySource_eq_belinskiZakharovResidue
    (coefficient : ℝ) :
    coefficient • Matrix.vecMulVec (ShiftedJacobiFrame.boundaryUnit 1)
      (ShiftedJacobiFrame.boundaryUnit 1) =
      belinskiZakharovRankOneResidue ![0, coefficient] ![0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ShiftedJacobiFrame.boundaryUnit, belinskiZakharovRankOneResidue, Matrix.vecMulVec]

/-- The first nontrivial shifted Xi Jacobi compression evolves by its Riccati law with an explicit
BZ rank-one boundary residue. -/
theorem ShiftedJacobiFrame.xiShiftedJacobi_twoLevelVelocity_eq_belinskiZakharovResidue
    (F : ShiftedJacobiFrame) (y : ℝ) :
    F.jacobiVelocityLevel 1 y =
      F.jacobiLevel 1 y * F.connectionLevel 1 y - F.connectionLevel 1 y * F.jacobiLevel 1 y
        - F.jacobiLevel 1 y * F.jacobiLevel 1 y
        - belinskiZakharovRankOneResidue
            ![0, 2 * ((1 : ℝ) + 1) * F.a (1 + 1) y ^ (2 : ℕ)] ![0, 1] := by
  rw [F.jacobiVelocityLevel_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ShiftedJacobiFrame.boundaryUnit, belinskiZakharovRankOneResidue,
      Matrix.vecMulVec]

end RHTower
