import GaloisForLFunctions.HTGeometry.HaferkampLiftedCliffordAction

/-!
# Terminal local Pauli coordinates for a light-cone block

Appendix B varies the final root-targeting local gate in the Hermitian
direction `I ⊗ Z`.  This file proves that its lifted ambient variation is
exactly the global root-only finite Pauli `Z` multiplied by that gate's
register lift.  It is the matrix identity underlying equation (B6).
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Lift an arbitrary two-qubit ambient matrix to a pair of register
coordinates, without imposing unitarity or determinant conditions. -/
def twoQubitLiftMatrix
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (M : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    Matrix (Q → Bool) (Q → Bool) ℂ :=
  Matrix.reindex (splitTwoQubitConfig a b hab).symm
    (splitTwoQubitConfig a b hab).symm (Matrix.kronecker M 1)

/-- The arbitrary ambient lift respects left multiplication by an `SU(4)`
gate. -/
theorem twoQubitLiftMatrix_mul_specialUnitary
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (M : Matrix (Bool × Bool) (Bool × Bool) ℂ)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    twoQubitLiftMatrix a b hab (M * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      twoQubitLiftMatrix a b hab M *
        (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) := by
  unfold twoQubitLiftMatrix
  have hlift : (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      Matrix.reindex (splitTwoQubitConfig a b hab).symm
        (splitTwoQubitConfig a b hab).symm
        (Matrix.kronecker (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) 1) := by
    rfl
  rw [hlift]
  calc
    Matrix.reindex (splitTwoQubitConfig a b hab).symm
        (splitTwoQubitConfig a b hab).symm
        (Matrix.kronecker (M * (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) 1) =
      Matrix.reindex (splitTwoQubitConfig a b hab).symm
        (splitTwoQubitConfig a b hab).symm
        (Matrix.kronecker M 1 *
          Matrix.kronecker (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) 1) := by
          conv_lhs => rw [show (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
            ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ) = 1 * 1 by simp]
          congr 1
          exact Matrix.mul_kronecker_mul M
            (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)
            (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
              ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)
            (1 : Matrix ({q : Q // q ≠ a ∧ q ≠ b} → Bool)
              ({q : Q // q ≠ a ∧ q ≠ b} → Bool) ℂ)
    _ = Matrix.reindex (splitTwoQubitConfig a b hab).symm
        (splitTwoQubitConfig a b hab).symm (Matrix.kronecker M 1) *
      Matrix.reindex (splitTwoQubitConfig a b hab).symm
        (splitTwoQubitConfig a b hab).symm
          (Matrix.kronecker (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) 1) := by
          change (Matrix.reindexLinearEquiv ℂ ℂ
            (splitTwoQubitConfig a b hab).symm (splitTwoQubitConfig a b hab).symm)
              (Matrix.kronecker M 1 *
                Matrix.kronecker (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) 1) = _
          exact (Matrix.reindexLinearEquiv_mul ℂ ℂ
            (splitTwoQubitConfig a b hab).symm (splitTwoQubitConfig a b hab).symm
            (splitTwoQubitConfig a b hab).symm (Matrix.kronecker M 1)
            (Matrix.kronecker (U : Matrix (Bool × Bool) (Bool × Bool) ℂ) 1)).symm

/-- The lifted local direction `I ⊗ Z` is the literal finite Pauli matrix
that is identity off the target coordinate and `Z` on it. -/
theorem twoQubitLiftMatrix_root_Z
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b) :
    twoQubitLiftMatrix a b hab (boolTwoQubitPauli none (some 2)) =
      finitePauliMatrix
        (updateTwoQubitPauliLabel (fun _ : Q => none) a b none (some 2)) := by
  apply (Matrix.reindexAlgEquiv ℂ ℂ (splitTwoQubitConfig a b hab)).injective
  change Matrix.reindex (splitTwoQubitConfig a b hab) (splitTwoQubitConfig a b hab)
      (twoQubitLiftMatrix a b hab (boolTwoQubitPauli none (some 2))) = _
  unfold twoQubitLiftMatrix
  change (Matrix.reindexLinearEquiv ℂ ℂ
      (splitTwoQubitConfig a b hab) (splitTwoQubitConfig a b hab))
      ((Matrix.reindexLinearEquiv ℂ ℂ
        (splitTwoQubitConfig a b hab).symm (splitTwoQubitConfig a b hab).symm)
        (Matrix.kronecker (boolTwoQubitPauli none (some 2)) 1)) = _
  rw [Matrix.reindexLinearEquiv_comp_apply]
  simp only [Equiv.symm_trans_self, Matrix.coe_reindexAlgEquiv]
  rw [reindex_splitTwoQubitConfig_finitePauliMatrix]
  have hrest : twoQubitRestPauliLabel (fun _ : Q => none) a b =
      fun _ => none := by
    funext q
    simp [twoQubitRestPauliLabel]
  rw [twoQubitRestPauliLabel_update, hrest, haferkamp_finitePauliMatrix_const_none]
  have hupdatea : updateTwoQubitPauliLabel (fun _ : Q => none) a b none (some 2) a = none := by
    simp [updateTwoQubitPauliLabel, hab]
  have hupdateb : updateTwoQubitPauliLabel (fun _ : Q => none) a b none (some 2) b = some 2 := by
    simp [updateTwoQubitPauliLabel]
  rw [hupdatea, hupdateb]
  simp

/-- The final local `I ⊗ Z` variation is global root-Pauli multiplication
immediately after its root-targeting two-qubit gate. -/
theorem twoQubitLiftMatrix_terminal_coordinate
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (a b : Q) (hab : a ≠ b)
    (U : Matrix.specialUnitaryGroup (Bool × Bool) ℂ) :
    twoQubitLiftMatrix a b hab
      (boolTwoQubitPauli none (some 2) *
        (U : Matrix (Bool × Bool) (Bool × Bool) ℂ)) =
      finitePauliMatrix
        (updateTwoQubitPauliLabel (fun _ : Q => none) a b none (some 2)) *
        (twoQubitLift a b hab U : Matrix (Q → Bool) (Q → Bool) ℂ) := by
  rw [twoQubitLiftMatrix_mul_specialUnitary, twoQubitLiftMatrix_root_Z]

end

end GaloisForLFunctions.HTGeometry
