import GaloisForLFunctions.HTGeometry.DifferentialTangentAdjoint
import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialBaseChange

/-!
# Translating a differential polynomial in the matrix entries

For a fixed matrix over the base field, the entries of `a·X` and of `X·b` are base-linear in the
entries of `X`, so substituting them is an evaluation of the differential polynomial ring in itself.
Because the translating matrix has entries in the base, the substituted polynomial again has base
coefficients, and its value at a matrix over *any* differential base algebra is the value of the
original at the translated matrix.

* `matrixLeftTranslate`, `matrixRightTranslate`;
* `evalOver_matrixLeftTranslate`, `evalOver_matrixRightTranslate`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

variable {C : Type*} [CommRing C] [Differential C]

/-- Differential polynomials over a differential base form a differential algebra over it. -/
local instance differentialPolynomialIsDifferentialAlgebra (ι : Type*) :
    DifferentialAlgebra C (DifferentialPolynomial ι C) where
  deriv_algebraMap a := by
    show differentialPolynomialOverDerivation ι C (MvPolynomial.C a) = MvPolynomial.C (a′)
    rw [differentialPolynomialOverDerivation_C]

variable {A : Type*} [CommRing A] [Algebra C A] [Differential A] [DifferentialAlgebra C A]

/-- The evaluation of a differential polynomial in the matrix entries, as a ring homomorphism. -/
private def matrixEvalHom (x : Matrix (Fin 2) (Fin 2) A) :
    DifferentialPolynomial (Fin 2 × Fin 2) C →+* A :=
  (differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)).toRingHom

private theorem matrixEvalHom_deriv (x : Matrix (Fin 2) (Fin 2) A)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    matrixEvalHom (C := C) x (P′) = (matrixEvalHom (C := C) x P)′ :=
  differentialPolynomialEvalOver_derivation (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2) P

omit [Differential C] [DifferentialAlgebra C A] in
private theorem matrixEvalHom_algebraMap (x : Matrix (Fin 2) (Fin 2) A) (c : C) :
    matrixEvalHom (C := C) x (algebraMap C (DifferentialPolynomial (Fin 2 × Fin 2) C) c)
      = algebraMap C A c := by
  show differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)
    (algebraMap C (DifferentialPolynomial (Fin 2 × Fin 2) C) c) = algebraMap C A c
  rw [MvPolynomial.algebraMap_eq, differentialPolynomialEvalOver_C]

/-- Left translation of a differential polynomial in the matrix entries. -/
def matrixLeftTranslate (a : Matrix (Fin 2) (Fin 2) C)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) : DifferentialPolynomial (Fin 2 × Fin 2) C :=
  differentialPolynomialEvalOver (K := C)
    (fun q : Fin 2 × Fin 2 => ∑ l : Fin 2,
      MvPolynomial.C (a q.1 l) * MvPolynomial.X (((l, q.2), 0) : (Fin 2 × Fin 2) × ℕ)) P

/-- Right translation of a differential polynomial in the matrix entries. -/
def matrixRightTranslate (b : Matrix (Fin 2) (Fin 2) C)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) : DifferentialPolynomial (Fin 2 × Fin 2) C :=
  differentialPolynomialEvalOver (K := C)
    (fun q : Fin 2 × Fin 2 => ∑ l : Fin 2,
      MvPolynomial.C (b l q.2) * MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ)) P

/-- **Evaluating the left translate is evaluating at the translated matrix**, over any differential
base algebra. -/
theorem evalOver_matrixLeftTranslate (a : Matrix (Fin 2) (Fin 2) C)
    (x : Matrix (Fin 2) (Fin 2) A) (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)
        (matrixLeftTranslate a P)
      = differentialPolynomialEvalOver (K := C)
          (fun q : Fin 2 × Fin 2 => ((a.map (algebraMap C A)) * x) q.1 q.2) P := by
  have hmap := map_differentialPolynomialEvalOver (matrixEvalHom (C := C) x)
    (matrixEvalHom_deriv (C := C) x) (matrixEvalHom_algebraMap (C := C) x)
    (fun q : Fin 2 × Fin 2 => ∑ l : Fin 2,
      MvPolynomial.C (a q.1 l) * MvPolynomial.X (((l, q.2), 0) : (Fin 2 × Fin 2) × ℕ)) P
  have hpt : (fun q : Fin 2 × Fin 2 => matrixEvalHom (C := C) x (∑ l : Fin 2,
      MvPolynomial.C (a q.1 l) * MvPolynomial.X (((l, q.2), 0) : (Fin 2 × Fin 2) × ℕ)))
      = fun q : Fin 2 × Fin 2 => ((a.map (algebraMap C A)) * x) q.1 q.2 := by
    funext q
    show differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
      (∑ l : Fin 2, MvPolynomial.C (a q.1 l)
        * MvPolynomial.X (((l, q.2), 0) : (Fin 2 × Fin 2) × ℕ)) = _
    rw [map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
      differentialJet_zero, Matrix.map_apply]
  rw [matrixLeftTranslate]
  refine hmap.trans ?_
  rw [hpt]

/-- **Evaluating the right translate is evaluating at the translated matrix**, over any differential
base algebra. -/
theorem evalOver_matrixRightTranslate (b : Matrix (Fin 2) (Fin 2) C)
    (x : Matrix (Fin 2) (Fin 2) A) (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)
        (matrixRightTranslate b P)
      = differentialPolynomialEvalOver (K := C)
          (fun q : Fin 2 × Fin 2 => (x * (b.map (algebraMap C A))) q.1 q.2) P := by
  have hmap := map_differentialPolynomialEvalOver (matrixEvalHom (C := C) x)
    (matrixEvalHom_deriv (C := C) x) (matrixEvalHom_algebraMap (C := C) x)
    (fun q : Fin 2 × Fin 2 => ∑ l : Fin 2,
      MvPolynomial.C (b l q.2) * MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ)) P
  have hpt : (fun q : Fin 2 × Fin 2 => matrixEvalHom (C := C) x (∑ l : Fin 2,
      MvPolynomial.C (b l q.2) * MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ)))
      = fun q : Fin 2 × Fin 2 => (x * (b.map (algebraMap C A))) q.1 q.2 := by
    funext q
    show differentialPolynomialEvalOver (K := C) (fun r : Fin 2 × Fin 2 => x r.1 r.2)
      (∑ l : Fin 2, MvPolynomial.C (b l q.2)
        * MvPolynomial.X (((q.1, l), 0) : (Fin 2 × Fin 2) × ℕ)) = _
    rw [map_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, differentialPolynomialEvalOver_C, differentialPolynomialEvalOver_X,
      differentialJet_zero, Matrix.map_apply]
    ring
  rw [matrixRightTranslate]
  refine hmap.trans ?_
  rw [hpt]


omit [Differential C] in
theorem matrix_map_algebraMap_self (a : Matrix (Fin 2) (Fin 2) C) :
    a.map (algebraMap C C) = a := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Algebra.algebraMap_self_apply]

/-- The left translate evaluated at a matrix over the base itself. -/
theorem evalOver_matrixLeftTranslate_self (a x : Matrix (Fin 2) (Fin 2) C)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)
        (matrixLeftTranslate a P)
      = differentialPolynomialEvalOver (K := C)
          (fun q : Fin 2 × Fin 2 => (a * x) q.1 q.2) P := by
  rw [evalOver_matrixLeftTranslate, matrix_map_algebraMap_self]

/-- The right translate evaluated at a matrix over the base itself. -/
theorem evalOver_matrixRightTranslate_self (b x : Matrix (Fin 2) (Fin 2) C)
    (P : DifferentialPolynomial (Fin 2 × Fin 2) C) :
    differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => x q.1 q.2)
        (matrixRightTranslate b P)
      = differentialPolynomialEvalOver (K := C)
          (fun q : Fin 2 × Fin 2 => (x * b) q.1 q.2) P := by
  rw [evalOver_matrixRightTranslate, matrix_map_algebraMap_self]

end

end GaloisForLFunctions.HTGeometry
