import GaloisForLFunctions.HTGeometry.LoopEisenstein.IwahoriLatticeChain

/-!
# Reversing a residual extension by changing lattices

The matrices `[a, q b; c, d]` and `[a, b; q c, d]` intertwine through
`diag(1,q)`. They have the same trace and determinant, while specialization
at `q=0` exchanges the stable coordinate line. At a repeated eigenvalue,
one lattice can have a scalar residual action and the other a nonzero
nilpotent extension.

This is the lattice mechanism of Polo–Rivero, §3.4, applied to the existing
Laurent Iwahori lattice chain.
-/

namespace GaloisForLFunctions.EisensteinDegeneration

open Matrix PowerSeries
open GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

section Ring

variable {R : Type*} [CommRing R]

/-- Integral action before enlarging the second basis vector. -/
def compactAction (q a b c d : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, q * b; c, d]

/-- Integral action after enlarging the second basis vector by `q⁻¹`. -/
def openAction (q a b c d : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, b; q * c, d]

/-- The inclusion of lattices is equivariant before inverting the uniformizer. -/
theorem lattice_extension_intertwines (q a b c d : R) :
    !![1, 0; 0, q] * compactAction q a b c d =
      openAction q a b c d * !![1, 0; 0, q] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [compactAction, openAction, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- The boundary extension is invisible to the determinant of the generic action. -/
theorem lattice_extension_det (q a b c d : R) :
    (compactAction q a b c d).det = (openAction q a b c d).det := by
  simp [compactAction, openAction, Matrix.det_fin_two, mul_assoc, mul_left_comm]

/-- The same is true of the trace. -/
theorem lattice_extension_trace (q a b c d : R) :
    (compactAction q a b c d).trace = (openAction q a b c d).trace := by
  simp [compactAction, openAction, Matrix.trace, Fin.sum_univ_two]

end Ring

section Specialization

variable {K : Type*} [Field K]

/-- The residual action on a power-series lattice. -/
def residualAction (A : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    Matrix (Fin 2) (Fin 2) K := A.map constantCoeff

theorem compactAction_residue (m : ℕ) (a b c d : PowerSeries K) :
    residualAction (compactAction (X ^ (m + 1)) a b c d) =
      !![constantCoeff a, 0; constantCoeff c, constantCoeff d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residualAction, compactAction]

theorem openAction_residue (m : ℕ) (a b c d : PowerSeries K) :
    residualAction (openAction (X ^ (m + 1)) a b c d) =
      !![constantCoeff a, constantCoeff b; 0, constantCoeff d] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residualAction, openAction]

/-- Before changing lattices, the second residual coordinate carries the character `d(0)`. -/
theorem compactAction_stable_line (m : ℕ) (a b c d : PowerSeries K) :
    residualAction (compactAction (X ^ (m + 1)) a b c d) *ᵥ ![0, 1] =
      constantCoeff d • ![0, 1] := by
  rw [compactAction_residue]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- After changing lattices, the first residual coordinate carries the character `a(0)`. -/
theorem openAction_stable_line (m : ℕ) (a b c d : PowerSeries K) :
    residualAction (openAction (X ^ (m + 1)) a b c d) *ᵥ ![1, 0] =
      constantCoeff a • ![1, 0] := by
  rw [openAction_residue]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The existing adjacent Iwahori lattice change recovers the integral compact action. -/
theorem iwahori_lattice_extension (a b c d : PowerSeries K) :
    latticeConjugate K
        ((openAction X a b c d).map (HahnSeries.ofPowerSeries ℤ K)) =
      (compactAction X a b c d).map (HahnSeries.ofPowerSeries ℤ K) := by
  rw [latticeConjugate_entries]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [compactAction, openAction, ← mul_assoc, HahnSeries.single_mul_single,
      ← HahnSeries.C_apply]

/-- A repeated residual character can be split in the smaller lattice. -/
theorem compactAction_scalar_residue (m : ℕ) (α : K) :
    residualAction (compactAction (X ^ (m + 1)) (C α) 1 0 (C α)) =
      α • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [compactAction_residue]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- In the larger lattice, the very same generic action retains a nonzero extension. -/
theorem openAction_scalar_residue_defect (m : ℕ) (α : K) :
    residualAction (openAction (X ^ (m + 1)) (C α) 1 0 (C α)) -
      α • (1 : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 0, 0] := by
  rw [openAction_residue]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Generic trace and determinant cannot decide whether the residual repeated character splits:
the new residual defect is nonzero but squares to zero at every boundary depth. -/
theorem lattice_change_creates_residual_extension (m : ℕ) (α : K) :
    let N := residualAction (openAction (X ^ (m + 1)) (C α) 1 0 (C α)) -
      α • (1 : Matrix (Fin 2) (Fin 2) K)
    N ^ 2 = 0 ∧ N ≠ 0 := by
  dsimp only
  rw [openAction_scalar_residue_defect]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) h
    exact one_ne_zero h01

end Specialization

end

end GaloisForLFunctions.EisensteinDegeneration
