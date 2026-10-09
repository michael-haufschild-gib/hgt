import GaloisForLFunctions.HTGeometry.SymmetricSquareMatrix
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Discriminant of the native symmetric-square representation

The binary quadratic discriminant is a determinant-square semi-invariant over
every commutative ring, including characteristic two. These identities supply
the native invariant whose actual normal class is preserved by the source Rees map.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Binary quadratic discriminant in the native symmetric-pair coordinate convention. -/
def paperSymmetricDiscriminant (c : Fin 3 → R) : R := c 1 ^ 2 - 4 * c 0 * c 2

/-- For the existing symmetric pair, the discriminant is the square of the pair determinant. -/
theorem paperSymmetricDiscriminant_pair (x y : Fin 2 → R) :
    paperSymmetricDiscriminant (symmetricPair x y) = (x 0 * y 1 - x 1 * y 0) ^ 2 := by
  simp [paperSymmetricDiscriminant, symmetricPair]
  ring

/-- The actual symmetric-square matrix preserves the discriminant up to determinant square. -/
theorem paperSymmetricDiscriminant_mulVec (S : Matrix (Fin 2) (Fin 2) R) (c : Fin 3 → R) :
    paperSymmetricDiscriminant ((symmetricSquareMatrix S).mulVec c) =
      S.det ^ 2 * paperSymmetricDiscriminant c := by
  simp [paperSymmetricDiscriminant, symmetricSquareMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.det_fin_two]
  ring

/-- Discriminants commute with coefficient-ring homomorphisms. -/
theorem paperSymmetricDiscriminant_map {A : Type*} [CommRing A] (f : R →+* A) (c : Fin 3 → R) :
    paperSymmetricDiscriminant (fun i => f (c i)) = f (paperSymmetricDiscriminant c) := by
  simp only [paperSymmetricDiscriminant, map_sub, map_mul, map_pow, map_ofNat]

/-- Scalar extension preserves the determinant-square law for the symmetric-square action. -/
theorem paperSymmetricDiscriminant_smul {A : Type*} [CommRing A] [Algebra R A]
    (S : Matrix (Fin 2) (Fin 2) R) (c : Fin 3 → A) :
    paperSymmetricDiscriminant (fun i => ∑ j, symmetricSquareMatrix S i j • c j) =
      (algebraMap R A S.det) ^ 2 * paperSymmetricDiscriminant c := by
  let f : R →+* A := algebraMap R A
  have hm := symmetricSquareMatrix_map f S
  have hd : (S.map f).det = f S.det := (f.map_det S).symm
  have hv : (fun i => ∑ j, symmetricSquareMatrix S i j • c j) =
      (symmetricSquareMatrix (S.map f)).mulVec c := by
    funext i
    change (∑ j, symmetricSquareMatrix S i j • c j) =
      ∑ j, symmetricSquareMatrix (S.map f) i j * c j
    apply Finset.sum_congr rfl
    intro j _
    rw [Algebra.smul_def]
    exact congrArg (fun z => z * c j) (congrFun (congrFun hm i) j)
  rw [hv, paperSymmetricDiscriminant_mulVec, hd]

/-- The native special-linear representation preserves the discriminant exactly. -/
theorem paperSymmetricDiscriminant_specialLinear (S : Matrix.SpecialLinearGroup (Fin 2) R)
    (c : Fin 3 → R) :
    paperSymmetricDiscriminant ((symmetricSquareMatrix (S : Matrix (Fin 2) (Fin 2) R)).mulVec c) =
      paperSymmetricDiscriminant c := by
  rw [paperSymmetricDiscriminant_mulVec, S.det_coe, one_pow, one_mul]

end GaloisForLFunctions.HTGeometry
