import GaloisForLFunctions.RHTower.BelinskiZakharovXiShiftedJacobiBridge
import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Separation of the Xi Jacobi and nilpotent BZ residue sectors

At two Jacobi levels, the shifted-Xi terminal boundary term is rank one, but it
is a coordinate projector residue.  The BZ Lax residue is rank-one nilpotent.
Their equality therefore forces both coefficients to vanish.  This identifies
the exact common boundary of the two rank-one models.

No relation to RH or to a curved gravitational inverse-scattering solution is
asserted.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open scoped Matrix

/-- The two-level shifted-Xi Jacobi boundary residue in its BZ rank-one coordinates. -/
def xiShiftedJacobiTwoLevelBelinskiZakharovResidue
    (coefficient : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovRankOneResidue ![0, coefficient] ![0, 1]

/-- The Jacobi boundary residue obeys the rank-one projector square law. -/
theorem xiShiftedJacobiTwoLevelBelinskiZakharovResidue_sq
    (coefficient : ℝ) :
    xiShiftedJacobiTwoLevelBelinskiZakharovResidue coefficient *
        xiShiftedJacobiTwoLevelBelinskiZakharovResidue coefficient =
      coefficient • xiShiftedJacobiTwoLevelBelinskiZakharovResidue coefficient := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xiShiftedJacobiTwoLevelBelinskiZakharovResidue,
      belinskiZakharovRankOneResidue, Matrix.vecMulVec, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- A two-level Xi Jacobi boundary residue equals a nilpotent BZ Lax residue exactly in the zero
sector.  Thus generic rank-one boundary forcing cannot be substituted into the nilpotent Lax
compatibility family. -/
theorem xiShiftedJacobiTwoLevelBelinskiZakharovResidue_eq_nilpotent_iff
    (coefficient residue : ℝ) :
    xiShiftedJacobiTwoLevelBelinskiZakharovResidue coefficient =
      belinskiZakharovNilpotentResidue residue ↔
      coefficient = 0 ∧ residue = 0 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    have h11 := congrFun (congrFun h 1) 1
    constructor
    · simpa [xiShiftedJacobiTwoLevelBelinskiZakharovResidue,
        belinskiZakharovRankOneResidue, belinskiZakharovNilpotentResidue,
        Matrix.vecMulVec] using h11
    · simpa [xiShiftedJacobiTwoLevelBelinskiZakharovResidue,
        belinskiZakharovRankOneResidue, belinskiZakharovNilpotentResidue,
        Matrix.vecMulVec] using h01.symm
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [xiShiftedJacobiTwoLevelBelinskiZakharovResidue,
        belinskiZakharovRankOneResidue, belinskiZakharovNilpotentResidue,
        Matrix.vecMulVec]

/-- The original two-level shifted-Xi Jacobi boundary source meets the canonical nilpotent BZ
residue family only at the zero coefficient. -/
theorem xiShiftedJacobi_boundarySource_eq_nilpotent_iff
    (coefficient residue : ℝ) :
    coefficient • Matrix.vecMulVec (ShiftedJacobiFrame.boundaryUnit 1)
        (ShiftedJacobiFrame.boundaryUnit 1) = belinskiZakharovNilpotentResidue residue ↔
      coefficient = 0 ∧ residue = 0 := by
  rw [xiShiftedJacobi_boundarySource_eq_belinskiZakharovResidue]
  exact xiShiftedJacobiTwoLevelBelinskiZakharovResidue_eq_nilpotent_iff coefficient residue

end RHTower
