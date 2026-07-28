import Mathlib

/-!
# Same-corner weak--Lorentz overlap

The standard action of `SU(2)` on the Hermitian `2 × 2` complex matrices is conjugation.
That same Hermitian matrix space is the Pauli-matrix model of four-dimensional Minkowski
space, where this action is the compact rotation subgroup of the Lorentz action.

This file records a concrete obstruction to treating this `SU(2)` action as an internal
pointwise kernel on the very same matrix corner.  The diagonal special-unitary matrix
`diag(i, -i)` sends the Pauli matrix `σ₁` to `-σ₁`, so its conjugation action is nontrivial.
All claims are finite exact matrix identities; no physical reconstruction premise is encoded.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Matrix

/-- The special-unitary half-turn `diag(i, -i)`. -/
def weakHalfTurn : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0;
     0, -Complex.I]

/-- The first Pauli matrix, viewed as a Hermitian spacetime coordinate. -/
def weakLorentzPauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1;
     1, 0]

/-- Conjugation action of a complex matrix on a `2 × 2` observable. -/
noncomputable def qubitConjugation
    (U X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  U * X * U.conjTranspose

/-- The half-turn is unitary. -/
theorem weakHalfTurn_conjTranspose_mul_self :
    weakHalfTurn.conjTranspose * weakHalfTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakHalfTurn, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The half-turn has determinant one.  Together with unitarity, this is its exact `SU(2)`
certificate without depending on a particular bundled-group representation. -/
theorem det_weakHalfTurn :
    Matrix.det weakHalfTurn = 1 := by
  simp [weakHalfTurn, Matrix.det_fin_two, Complex.I_mul_I]

/-- The selected Pauli spacetime coordinate is Hermitian. -/
theorem weakLorentzPauliX_conjTranspose :
    weakLorentzPauliX.conjTranspose = weakLorentzPauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weakLorentzPauliX, Matrix.conjTranspose_apply]

/-- The special-unitary half-turn reverses the selected Pauli coordinate. -/
theorem weakHalfTurn_conjugates_pauliX :
    qubitConjugation weakHalfTurn weakLorentzPauliX = -weakLorentzPauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitConjugation, weakHalfTurn, weakLorentzPauliX, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.I_mul_I]

/-- The special-unitary half-turn does not fix the selected Pauli coordinate. -/
theorem weakHalfTurn_conjugation_ne :
    qubitConjugation weakHalfTurn weakLorentzPauliX ≠ weakLorentzPauliX := by
  intro h
  have h01 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
  simp [qubitConjugation, weakHalfTurn, weakLorentzPauliX, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.I_mul_I] at h01
  norm_num at h01

/-- Consequently, the whole conjugation action cannot be the identity on the same Hermitian
matrix corner. -/
theorem weakHalfTurn_not_in_sameCorner_pointwiseKernel :
    ¬ ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
        qubitConjugation weakHalfTurn X = X := by
  intro h
  exact weakHalfTurn_conjugation_ne (h weakLorentzPauliX)

end GaloisForLFunctions.HTGeometry
