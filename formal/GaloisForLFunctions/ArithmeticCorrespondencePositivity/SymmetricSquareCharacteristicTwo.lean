import GaloisForLFunctions.RepresentationLifting.QuadraticSequence
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.SymmetricSquareDiscriminant

/-!
# The Frobenius plane and determinant quotient of a binary symmetric square

In characteristic two, the pure squares form a Frobenius-twisted plane, and the mixed
coefficient transforms by the determinant. The discriminant conic is the double of that plane.
This specializes the quadratic sequence of Scavia §3.1 to the symmetric-square and Hecke
matrices used for arithmetic correspondences.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open HTGeometry

variable {R : Type*} [CommRing R]

/-- Pure-square coefficients in binary quadratic-product coordinates. -/
def binarySquareDiagonal : (Fin 2 → R) →ₗ[R] (Fin 3 → R) where
  toFun x := ![x 0, 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- The mixed coefficient of a binary quadratic product. -/
def binaryMixed : (Fin 3 → R) →ₗ[R] R := LinearMap.proj 1

/-- The quotient by the pure-square plane is exactly the mixed coefficient. -/
theorem binarySquareDiagonal_exact :
    Function.Injective (binarySquareDiagonal (R := R)) ∧
      LinearMap.range binarySquareDiagonal = LinearMap.ker (binaryMixed (R := R)) ∧
      Function.Surjective (binaryMixed (R := R)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    funext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 2
  · ext v
    constructor
    · rintro ⟨x, rfl⟩; rfl
    · intro h
      have hv : v 1 = 0 := h
      refine ⟨![v 0, v 2], ?_⟩
      ext i
      fin_cases i <;> simp [binarySquareDiagonal, hv]
  · intro a
    exact ⟨![0, a, 0], rfl⟩

variable [CharP R 2]

/-- The action on the pure-square plane is the entrywise Frobenius twist. -/
theorem binarySquareDiagonal_intertwines (A : Matrix (Fin 2) (Fin 2) R) (x : Fin 2 → R) :
    (symmetricSquareMatrix A).mulVec (binarySquareDiagonal x) =
      binarySquareDiagonal ((A.map (fun a => a ^ 2)).mulVec x) := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  ext i
  fin_cases i <;>
    simp [binarySquareDiagonal, symmetricSquareMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, h2]

/-- The one-dimensional quotient carries the determinant character. -/
theorem binaryMixed_intertwines (A : Matrix (Fin 2) (Fin 2) R) (v : Fin 3 → R) :
    binaryMixed ((symmetricSquareMatrix A).mulVec v) = A.det * binaryMixed v := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  simp [binaryMixed, symmetricSquareMatrix, dotProduct,
    Fin.sum_univ_succ, Matrix.det_fin_two, h2, CharTwo.sub_eq_add]

/-- The characteristic-two discriminant is the square of the quotient coordinate. -/
theorem symmetricDiscriminant_charTwo (v : Fin 3 → R) :
    symmetricDiscriminant v = binaryMixed v ^ 2 := by
  have h4 : (4 : R) = 0 := by
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
    calc
      (4 : R) = 2 * 2 := by ring
      _ = 0 := by rw [h2, zero_mul]
  simp only [symmetricDiscriminant, binaryMixed, LinearMap.proj_apply, h4,
    zero_mul, sub_zero]

/-- Hecke companions act on the quotient by their determinant `p`. -/
theorem heckeCompanion_mixed_charTwo (a p : R) (v : Fin 3 → R) :
    binaryMixed
      ((symmetricSquareMatrix (!![a, -p; 1, 0] : Matrix (Fin 2) (Fin 2) R)).mulVec v) =
      p * binaryMixed v := by
  rw [binaryMixed_intertwines]
  simp [Matrix.det_fin_two]

/-- Over a field, the discriminant-zero locus is precisely the Frobenius plane. -/
theorem symmetricDiscriminant_zero_iff_frobeniusPlane
    {k : Type*} [Field k] [CharP k 2] (v : Fin 3 → k) :
    symmetricDiscriminant v = 0 ↔
      v ∈ LinearMap.range (binarySquareDiagonal (R := k)) := by
  rw [symmetricDiscriminant_charTwo, binarySquareDiagonal_exact.2.1]
  change binaryMixed v ^ 2 = 0 ↔ binaryMixed v = 0
  exact pow_eq_zero_iff (Nat.succ_ne_zero 1)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.binarySquareDiagonal_intertwines
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.binaryMixed_intertwines
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.heckeCompanion_mixed_charTwo
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.symmetricDiscriminant_zero_iff_frobeniusPlane
