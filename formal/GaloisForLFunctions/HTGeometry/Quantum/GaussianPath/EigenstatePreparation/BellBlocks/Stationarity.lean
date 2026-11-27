import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal

/-! # A commutator test for observables in every energy eigenstate -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Expectation of an observable in one normalized energy eigenvector. -/
def energyDiagonal (H : selfAdjoint (Mat I)) (A : Mat I) (i : I) : ℂ :=
  let V := H.2.isHermitian.eigenvectorUnitary
  (star V.val*A*V.val) i i

private theorem commutator_diagonal (H : selfAdjoint (Mat I)) (L : Mat I) (i : I) :
    energyDiagonal H (H.val*L-L*H.val) i=0 := by
  let V := H.2.isHermitian.eigenvectorUnitary
  let D := diagonal (fun i => (H.2.isHermitian.eigenvalues i:ℂ))
  let Z := star V.val*L*V.val
  have hH : H.val=V.val*D*star V.val := isHermitian_eq_conj_diagonal H.2.isHermitian
  have h₁ : star V.val*H.val=D*star V.val := by
    rw [hH,←mul_assoc,←mul_assoc,(Unitary.mem_iff.mp V.property).1,one_mul]
  have h₂ : H.val*V.val=V.val*D := by
    rw [hH,mul_assoc (V.val*D),(Unitary.mem_iff.mp V.property).1,mul_one]
  have he : star V.val*(H.val*L-L*H.val)*V.val=D*Z-Z*D := by
    rw [Matrix.mul_sub,Matrix.sub_mul,←mul_assoc (star V.val) H.val L,h₁]
    simp only [Z,mul_assoc,h₂]
  change (star V.val*(H.val*L-L*H.val)*V.val) i i=0
  rw [he,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm,sub_self]

/-- The diagonal signal of a model commutator costs at most twice the
Hamiltonian replacement error times the norm of its test operator.
Degenerate energy levels obey the same estimate. -/
theorem commutator_signal (H : selfAdjoint (Mat I)) (J L : Mat I) (i : I) :
    ‖energyDiagonal H (J*L-L*J) i‖ ≤ 2*‖J-H.val‖*‖L‖ := by
  letI : Nonempty I := ⟨i⟩
  let V := H.2.isHermitian.eigenvectorUnitary
  let A := (J-H.val)*L-L*(J-H.val)
  have he : J*L-L*J=A+(H.val*L-L*H.val) := by
    dsimp only [A]
    rw [Matrix.sub_mul,Matrix.mul_sub]
    abel
  have hsplit (X Y : Mat I) : energyDiagonal H (X+Y) i=energyDiagonal H X i+energyDiagonal H Y i := by
    simp only [energyDiagonal,Matrix.mul_add,Matrix.add_mul,Matrix.add_apply]
  rw [he,hsplit,commutator_diagonal,add_zero]
  calc
    ‖energyDiagonal H A i‖ ≤ ‖star V.val*A*V.val‖ := norm_entry_le_l2_opNorm _ i i
    _ = ‖A‖ := by simpa only [star_star] using l2_opNorm_unitary_conj_eq (Unitary.star_mem V.property) A
    _ ≤ ‖(J-H.val)*L‖+‖L*(J-H.val)‖ := norm_sub_le _ _
    _ ≤ _ := (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans_eq (by ring)

#print axioms commutator_signal
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
