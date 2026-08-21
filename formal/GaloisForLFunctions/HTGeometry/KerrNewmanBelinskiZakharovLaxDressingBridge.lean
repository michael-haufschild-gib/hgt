import GaloisForLFunctions.HTGeometry.KerrNewmanBelinskiZakharovBridge

/-!
# Gauge rigidity of the nilpotent Belinski--Zakharov Lax sector

The canonical rank-one BZ residue and every unipotent one-pole dressing lie in
the same one-dimensional nilpotent subgroup.  Consequently conjugating that
residue, and the two-coordinate Lax pair it generates, by any one-pole dressing
does not change it.  The zero-curvature equation therefore survives exactly.

This is an algebraic statement about the finite `2 x 2` model.  It does not say
that an arbitrary BZ dressing is gauge trivial, nor does it construct a curved
Einstein--Maxwell solution.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Conjugation by a one-pole BZ dressing, with its opposite residue as inverse. -/
def belinskiZakharovOnePoleConjugate
    (spectral pole dressingResidue : ℝ) (coefficient : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  belinskiZakharovOnePoleDressing spectral pole dressingResidue * coefficient *
    belinskiZakharovOnePoleDressing spectral pole (-dressingResidue)

/-- A one-pole dressing centralizes every canonical nilpotent BZ residue. -/
theorem belinskiZakharovOnePoleConjugate_nilpotentResidue
    (spectral pole dressingResidue residue : ℝ) :
    belinskiZakharovOnePoleConjugate spectral pole dressingResidue
      (belinskiZakharovNilpotentResidue residue) =
      belinskiZakharovNilpotentResidue residue := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovOnePoleConjugate, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, belinskiZakharovNilpotentResidue,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The axial coefficient of the nilpotent Lax pair after a one-pole BZ conjugation. -/
def belinskiZakharovOnePoleDressedNilpotentLaxU
    (spectral pole dressingResidue laxResidue : ℝ) :
    ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun rho z => belinskiZakharovOnePoleConjugate spectral pole dressingResidue
    (belinskiZakharovNilpotentLaxU laxResidue rho z)

/-- The radial coefficient of the nilpotent Lax pair after a one-pole BZ conjugation. -/
def belinskiZakharovOnePoleDressedNilpotentLaxV
    (spectral pole dressingResidue laxResidue : ℝ) :
    ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
  fun rho z => belinskiZakharovOnePoleConjugate spectral pole dressingResidue
    (belinskiZakharovNilpotentLaxV laxResidue rho z)

/-- The dressed axial coefficient is pointwise unchanged. -/
theorem belinskiZakharovOnePoleDressedNilpotentLaxU_eq
    (spectral pole dressingResidue laxResidue rho z : ℝ) :
    belinskiZakharovOnePoleDressedNilpotentLaxU spectral pole dressingResidue laxResidue rho z =
      belinskiZakharovNilpotentLaxU laxResidue rho z := by
  unfold belinskiZakharovOnePoleDressedNilpotentLaxU belinskiZakharovNilpotentLaxU
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovOnePoleConjugate, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, belinskiZakharovNilpotentResidue,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The dressed radial coefficient is pointwise unchanged. -/
theorem belinskiZakharovOnePoleDressedNilpotentLaxV_eq
    (spectral pole dressingResidue laxResidue rho z : ℝ) :
    belinskiZakharovOnePoleDressedNilpotentLaxV spectral pole dressingResidue laxResidue rho z =
      belinskiZakharovNilpotentLaxV laxResidue rho z := by
  unfold belinskiZakharovOnePoleDressedNilpotentLaxV belinskiZakharovNilpotentLaxV
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belinskiZakharovOnePoleConjugate, belinskiZakharovOnePoleDressing,
      belinskiZakharovUnipotentDressing, belinskiZakharovNilpotentResidue,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- **Gauge-rigid BZ Lax compatibility.**  Every spectral pole and dressing residue leaves the
canonical rank-one Lax zero-curvature equation unchanged. -/
theorem belinskiZakharovOnePoleDressedNilpotentLax_zeroCurvature
    (spectral pole dressingResidue laxResidue rho z : ℝ) :
    belinskiZakharovZeroCurvature
      (belinskiZakharovOnePoleDressedNilpotentLaxU spectral pole dressingResidue laxResidue)
      (belinskiZakharovOnePoleDressedNilpotentLaxV spectral pole dressingResidue laxResidue)
      rho z = 0 := by
  have hU : belinskiZakharovOnePoleDressedNilpotentLaxU spectral pole dressingResidue laxResidue =
      belinskiZakharovNilpotentLaxU laxResidue := by
    funext r w
    exact belinskiZakharovOnePoleDressedNilpotentLaxU_eq spectral pole dressingResidue laxResidue r w
  have hV : belinskiZakharovOnePoleDressedNilpotentLaxV spectral pole dressingResidue laxResidue =
      belinskiZakharovNilpotentLaxV laxResidue := by
    funext r w
    exact belinskiZakharovOnePoleDressedNilpotentLaxV_eq spectral pole dressingResidue laxResidue r w
  rw [hU, hV]
  exact belinskiZakharovNilpotentLax_zeroCurvature laxResidue rho z

end

end GaloisForLFunctions.HTGeometry
