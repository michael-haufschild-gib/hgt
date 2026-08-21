import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Algebra of two-Killing Belinski--Zakharov rank-one residues

A BZ column--row residue `u v^T` squares to the scalar contraction `v^T u`
times itself. Its square therefore vanishes exactly when that contraction does.
This is the finite rank-one constraint separating nilpotent BZ Lax residues from
generic rank-one projector residues.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- Row--column contraction controlling the square of a BZ rank-one residue. -/
def belinskiZakharovRankOneContraction
    (column row : Fin 2 → ℝ) : ℝ :=
  dotProduct row column

/-- The contraction is the matrix trace of the corresponding BZ rank-one residue. -/
theorem belinskiZakharovRankOneContraction_eq_trace
    (column row : Fin 2 → ℝ) :
    belinskiZakharovRankOneContraction column row =
      Matrix.trace (belinskiZakharovRankOneResidue column row) := by
  simp [belinskiZakharovRankOneContraction, belinskiZakharovRankOneResidue,
    Matrix.vecMulVec, dotProduct, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Every BZ column--row residue satisfies its exact rank-one square law. -/
theorem belinskiZakharovRankOneResidue_sq
    (column row : Fin 2 → ℝ) :
    belinskiZakharovRankOneResidue column row *
        belinskiZakharovRankOneResidue column row =
      belinskiZakharovRankOneContraction column row •
        belinskiZakharovRankOneResidue column row := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovRankOneContraction, belinskiZakharovRankOneResidue,
      Matrix.vecMulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- **Nilpotence criterion for BZ rank-one residues.** The square vanishes precisely when the
row--column contraction vanishes. -/
theorem belinskiZakharovRankOneResidue_sq_eq_zero_iff
    (column row : Fin 2 → ℝ) :
    belinskiZakharovRankOneResidue column row *
        belinskiZakharovRankOneResidue column row = 0 ↔
      belinskiZakharovRankOneContraction column row = 0 := by
  constructor
  · intro h
    rw [belinskiZakharovRankOneResidue_sq] at h
    rcases smul_eq_zero.mp h with hcontraction | hresidue
    · exact hcontraction
    · rw [belinskiZakharovRankOneContraction_eq_trace, hresidue]
      simp
  · intro h
    rw [belinskiZakharovRankOneResidue_sq, h]
    simp

/-- The canonical BZ nilpotent residue realizes the zero-contraction branch of the generic
rank-one criterion. -/
theorem belinskiZakharovNilpotentResidue_eq_zeroContractionRankOne
    (residue : ℝ) :
    belinskiZakharovRankOneContraction ![residue, 0] ![0, 1] = 0 := by
  simp [belinskiZakharovRankOneContraction, dotProduct, Fin.sum_univ_two]

end GaloisForLFunctions.HTGeometry
