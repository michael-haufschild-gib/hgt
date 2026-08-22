import GaloisForLFunctions.HTGeometry.HaferkampLiftedCliffordAction

/-!
# Signs in finite Pauli--Clifford transport

An exact unitary conjugation carries one literal Hermitian Pauli involution to
a scalar multiple of another.  The involution identity forces that scalar to
be a sign, not an arbitrary nonzero complex number.  This is the real-linear
phase control required by the state-complexity version of the Haferkamp
rank-witness construction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A scalar in an exact unitary conjugation between literal Pauli
involutions is necessarily a sign. -/
theorem pauli_conjugation_scalar_eq_one_or_neg_one
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Matrix.unitaryGroup (Q → Bool) ℂ)
    (P R : Q → Option (Fin 3)) (c : ℂ)
    (hconj : (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
        Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
      c • finitePauliMatrix R) :
    c = 1 ∨ c = -1 := by
  let M : Matrix (Q → Bool) (Q → Bool) ℂ :=
    (U : Matrix (Q → Bool) (Q → Bool) ℂ)
  have hUleft : M * Matrix.conjTranspose M = 1 := by
    change (U : Matrix (Q → Bool) (Q → Bool) ℂ) *
      Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) = 1
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.2
  have hUright : Matrix.conjTranspose M * M = 1 :=
    mul_eq_one_comm.mp hUleft
  have hleftsq : (M * finitePauliMatrix P * Matrix.conjTranspose M) *
      (M * finitePauliMatrix P * Matrix.conjTranspose M) = 1 := by
    calc
      (M * finitePauliMatrix P * Matrix.conjTranspose M) *
          (M * finitePauliMatrix P * Matrix.conjTranspose M) =
        M * finitePauliMatrix P * (Matrix.conjTranspose M * M) *
          finitePauliMatrix P * Matrix.conjTranspose M := by
            noncomm_ring
      _ = M * finitePauliMatrix P * 1 * finitePauliMatrix P *
          Matrix.conjTranspose M := by rw [hUright]
      _ = M * Matrix.conjTranspose M := by
        calc
          M * finitePauliMatrix P * 1 * finitePauliMatrix P *
              Matrix.conjTranspose M =
              M * (finitePauliMatrix P * finitePauliMatrix P) *
                Matrix.conjTranspose M := by
                  noncomm_ring
          _ = M * Matrix.conjTranspose M := by
            rw [finitePauliMatrix_mul_self, Matrix.mul_one]
      _ = 1 := hUleft
  have hcsq_matrix : (c ^ 2 : ℂ) •
      (1 : Matrix (Q → Bool) (Q → Bool) ℂ) = 1 := by
    have hsquares := congrArg
      (fun A : Matrix (Q → Bool) (Q → Bool) ℂ => A * A) hconj
    rw [hleftsq, Matrix.smul_mul, Matrix.mul_smul,
      finitePauliMatrix_mul_self] at hsquares
    simpa [pow_two, smul_smul] using hsquares.symm
  let x : Q → Bool := fun _ => false
  have hcsq : c ^ 2 = 1 := by
    have hx := congrFun (congrFun hcsq_matrix x) x
    simpa [Matrix.smul_apply] using hx
  exact sq_eq_one_iff.mp hcsq

/-- A finite Pauli--Clifford sends every literal Pauli to another one with a
literal sign coefficient. -/
theorem IsFinitePauliClifford.exists_signed_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {U : Matrix.unitaryGroup (Q → Bool) ℂ}
    (hU : IsFinitePauliClifford U) (P : Q → Option (Fin 3)) :
    ∃ c : ℂ, ∃ R : Q → Option (Fin 3),
      (c = 1 ∨ c = -1) ∧
      (U : Matrix (Q → Bool) (Q → Bool) ℂ) * finitePauliMatrix P *
          Matrix.conjTranspose (U : Matrix (Q → Bool) (Q → Bool) ℂ) =
        c • finitePauliMatrix R := by
  obtain ⟨c, R, _hc, hconj⟩ := hU P
  exact ⟨c, R, pauli_conjugation_scalar_eq_one_or_neg_one U P R c hconj, hconj⟩

end

end GaloisForLFunctions.HTGeometry
