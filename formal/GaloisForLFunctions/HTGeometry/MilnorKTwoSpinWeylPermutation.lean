import GaloisForLFunctions.HTGeometry.MilnorKTwoSpinWeylClassification

/-!
# Permutation quotient of the rank-four Spin-Weyl matrix group

Unique signed-monomial data define a canonical permutation homomorphism. Its kernel is exactly the
determinant-one diagonal sign subgroup, providing the quotient invariant needed for Milnor's
common-subgroup identification.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry
namespace MilnorSpinWeyl

private theorem exists_signedMonomialData
    (A : generatedSignedMonomialSubgroup) :
    ∃ q : Equiv.Perm (Fin 4) × (Fin 4 → ℝˣ),
      (∀ p, q.2 p = 1 ∨ q.2 p = -1) ∧
        (A.1 : Matrix (Fin 4) (Fin 4) ℝ) =
          signedMonomialMatrix q.1 q.2 := by
  obtain ⟨σ, c, hc, hA⟩ := generatedSignedMonomialSubgroup_isSignedMonomial A
  exact ⟨(σ, c), hc, hA⟩

/-- Canonical signed-monomial data of a rotor-generated matrix. -/
noncomputable def signedMonomialData (A : generatedSignedMonomialSubgroup) :
    Equiv.Perm (Fin 4) × (Fin 4 → ℝˣ) :=
  Classical.choose (exists_signedMonomialData A)

theorem signedMonomialData_signs (A : generatedSignedMonomialSubgroup) :
    ∀ p, (signedMonomialData A).2 p = 1 ∨
      (signedMonomialData A).2 p = -1 :=
  (Classical.choose_spec (exists_signedMonomialData A)).1

theorem signedMonomialData_matrix (A : generatedSignedMonomialSubgroup) :
    (A.1 : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix (signedMonomialData A).1
        (signedMonomialData A).2 :=
  (Classical.choose_spec (exists_signedMonomialData A)).2

theorem signedMonomialData_eq {A : generatedSignedMonomialSubgroup}
    {σ : Equiv.Perm (Fin 4)} {c : Fin 4 → ℝˣ}
    (hA : (A.1 : Matrix (Fin 4) (Fin 4) ℝ) =
      signedMonomialMatrix σ c) :
    (signedMonomialData A).1 = σ ∧ (signedMonomialData A).2 = c := by
  apply MilnorDiagonalExtension.signedMonomialMatrix_data_injective
  rw [← signedMonomialData_matrix A, hA]

/-- Permutation quotient of the determinant-one signed-monomial group. -/
noncomputable def signedMonomialPermutationHom :
    generatedSignedMonomialSubgroup →* Equiv.Perm (Fin 4) where
  toFun A := (signedMonomialData A).1
  map_one' :=
    (signedMonomialData_eq
      (A := (1 : generatedSignedMonomialSubgroup))
      (σ := 1) (c := fun _ => 1) (by
        simp [signedMonomialMatrix_one])).1
  map_mul' A B := by
    let c := (signedMonomialData A).2
    let d := (signedMonomialData B).2
    have hAB : (((A * B).1 :
        (Matrix (Fin 4) (Fin 4) ℝ)ˣ) : Matrix (Fin 4) (Fin 4) ℝ) =
        signedMonomialMatrix
          ((signedMonomialData A).1 * (signedMonomialData B).1)
          (fun p => c ((signedMonomialData B).1 p) * d p) := by
      change (A.1 : Matrix (Fin 4) (Fin 4) ℝ) *
        (B.1 : Matrix (Fin 4) (Fin 4) ℝ) = _
      rw [signedMonomialData_matrix A, signedMonomialData_matrix B,
        signedMonomialMatrix_mul]
      rfl
    exact (signedMonomialData_eq hAB).1

@[simp] theorem signedMonomialPermutationHom_apply
    (A : generatedSignedMonomialSubgroup) :
    signedMonomialPermutationHom A = (signedMonomialData A).1 := rfl

/-- Diagonal sign subgroup, intrinsically the permutation kernel. -/
def diagonalSignedMonomialSubgroup :
    Subgroup generatedSignedMonomialSubgroup :=
  signedMonomialPermutationHom.ker

theorem mem_diagonalSignedMonomialSubgroup_iff
    (A : generatedSignedMonomialSubgroup) :
    A ∈ diagonalSignedMonomialSubgroup ↔
      ∃ c : Fin 4 → ℝˣ, (∀ p, c p = 1 ∨ c p = -1) ∧
        (A.1 : Matrix (Fin 4) (Fin 4) ℝ) = signedMonomialMatrix 1 c := by
  constructor
  · intro hA
    refine ⟨(signedMonomialData A).2, signedMonomialData_signs A, ?_⟩
    have hperm : (signedMonomialData A).1 = 1 := hA
    simpa [hperm] using signedMonomialData_matrix A
  · rintro ⟨c, hc, hA⟩
    change signedMonomialPermutationHom A = 1
    exact (signedMonomialData_eq hA).1

end MilnorSpinWeyl
end GaloisForLFunctions.HTGeometry

end
