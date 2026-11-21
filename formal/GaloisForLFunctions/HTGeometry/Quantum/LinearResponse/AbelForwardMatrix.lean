import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingInverse
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Polynomial numerators of the forward Abel response

Column vectorization represents the commutator by a Kronecker matrix.
The adjugate clears the denominator, so the resulting numerator
commutes with coefficient specialization.
-/

open Matrix Set
open scoped Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]

/-- The matrix of the commutator (X \mapsto HX-XH) under column vectorization. -/
def commutatorKroneckerMatrix (H : Matrix ι ι R) : Matrix (ι × ι) (ι × ι) R :=
  (1 : Matrix ι ι R) ⊗ₖ H - Hᵀ ⊗ₖ (1 : Matrix ι ι R)

theorem commutatorKroneckerMatrix_mulVec_vec (H X : Matrix ι ι R) :
    commutatorKroneckerMatrix H *ᵥ X.vec = (H * X - X * H).vec := by
  rw [commutatorKroneckerMatrix, Matrix.sub_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.transpose_transpose,
    Matrix.mul_one, Matrix.one_mul, Matrix.vec_sub]

omit [Fintype ι] in
theorem map_commutatorKroneckerMatrix (f : R →+* S) (H : Matrix ι ι R) :
    (commutatorKroneckerMatrix H).map f = commutatorKroneckerMatrix (H.map f) := by
  ext ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
  simp only [commutatorKroneckerMatrix, Matrix.map_apply, Matrix.sub_apply,
    Matrix.kronecker_apply, Matrix.transpose_apply, Matrix.one_apply, map_sub,
    map_mul, apply_ite f, map_one, map_zero]

/-- The vectorized inverse response at inverse shift `γ`. -/
def abelForwardPencil (γ : R) (H : Matrix ι ι R) : Matrix (ι × ι) (ι × ι) R :=
  1 - γ • commutatorKroneckerMatrix H

theorem abelForwardPencil_mulVec_vec (γ : R) (H X : Matrix ι ι R) :
    abelForwardPencil γ H *ᵥ X.vec = (X - γ • (H * X - X * H)).vec := by
  simp only [abelForwardPencil, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    commutatorKroneckerMatrix_mulVec_vec, Matrix.vec_sub, Matrix.vec_smul]

omit [Fintype ι] in
theorem map_abelForwardPencil (f : R →+* S) (γ : R) (H : Matrix ι ι R) :
    (abelForwardPencil γ H).map f = abelForwardPencil (f γ) (H.map f) := by
  ext p q
  have h := congrArg (fun M : Matrix (ι × ι) (ι × ι) S => M p q)
    (map_commutatorKroneckerMatrix f H)
  change f (commutatorKroneckerMatrix H p q) = _ at h
  simp only [abelForwardPencil, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, map_sub, map_mul, apply_ite f, map_one, map_zero, h]

/-- The forward response multiplied by the determinant of its inverse pencil. -/
def abelClearedResponse (γ : R) (H X : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun i j => ((abelForwardPencil γ H).adjugate *ᵥ X.vec) (j, i)

theorem vec_abelClearedResponse (γ : R) (H X : Matrix ι ι R) :
    (abelClearedResponse γ H X).vec = (abelForwardPencil γ H).adjugate *ᵥ X.vec := rfl

theorem map_abelClearedResponse (f : R →+* S) (γ : R) (H X : Matrix ι ι R) :
    (abelClearedResponse γ H X).map f = abelClearedResponse (f γ) (H.map f) (X.map f) := by
  have h : (abelForwardPencil γ H).adjugate.map f =
      (abelForwardPencil (f γ) (H.map f)).adjugate := by
    calc
      _ = ((abelForwardPencil γ H).map f).adjugate :=
        f.map_adjugate (abelForwardPencil γ H)
      _ = _ := by rw [map_abelForwardPencil]
  ext i j
  simp only [abelClearedResponse, Matrix.map_apply, Matrix.of_apply, Matrix.mulVec, dotProduct,
    map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun M : Matrix (ι × ι) (ι × ι) S => M (j, i) k * f (X.vec k)) h

theorem abelClearedResponse_zeroParameter (H X : Matrix ι ι R) :
    abelClearedResponse 0 H X = X := by
  apply Matrix.vec_inj.mp
  rw [vec_abelClearedResponse, abelForwardPencil, zero_smul, sub_zero,
    Matrix.adjugate_one, Matrix.one_mulVec]

theorem abelClearedResponse_zeroHamiltonian (γ : R) (X : Matrix ι ι R) :
    abelClearedResponse γ 0 X = X := by
  apply Matrix.vec_inj.mp
  rw [vec_abelClearedResponse, abelForwardPencil, commutatorKroneckerMatrix,
    Matrix.transpose_zero, Matrix.kronecker_zero, Matrix.zero_kronecker, sub_zero,
    smul_zero, sub_zero, Matrix.adjugate_one, Matrix.one_mulVec]

theorem abelClearedResponse_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    abelClearedResponse (hamiltonianAbelShift ε)⁻¹ H X =
      (abelForwardPencil (hamiltonianAbelShift ε)⁻¹ H).det •
        hamiltonianDampedGapResponse hH 0 ε X := by
  let γ := (hamiltonianAbelShift ε)⁻¹
  let A := abelForwardPencil γ H
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  have hv : A *ᵥ Y.vec = X.vec := by
    change abelForwardPencil (hamiltonianAbelShift ε)⁻¹ H *ᵥ Y.vec = X.vec
    rw [abelForwardPencil_mulVec_vec, ← hamiltonianAbelInverse_eq_sub,
      hamiltonianAbelInverse_leftInverse hH ε X]
  apply Matrix.vec_inj.mp
  rw [vec_abelClearedResponse, Matrix.vec_smul]
  change A.adjugate *ᵥ X.vec = A.det • Y.vec
  rw [← hv, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem isUnit_abelForwardPencil {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    IsUnit (abelForwardPencil (hamiltonianAbelShift ε)⁻¹ H) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  obtain ⟨X, rfl⟩ := Matrix.vec_bijective.surjective x
  obtain ⟨Y, rfl⟩ := Matrix.vec_bijective.surjective y
  rw [abelForwardPencil_mulVec_vec, abelForwardPencil_mulVec_vec,
    ← hamiltonianAbelInverse_eq_sub, ← hamiltonianAbelInverse_eq_sub] at h
  exact congrArg Matrix.vec
    ((hamiltonianAbelInverse_rightInverse hH ε).injective (Matrix.vec_inj.mp h))

#print axioms abelClearedResponse_eq
#print axioms isUnit_abelForwardPencil
#print axioms map_abelClearedResponse

end GaloisForLFunctions.HTGeometry
