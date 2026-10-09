import GaloisForLFunctions.HTGeometry.PaperPluckerNormalRelations
import GaloisForLFunctions.HTGeometry.PaperNativeReesInitialLinearMap
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Row-change covariance of actual Plücker initial classes

Row changes may have polynomial entries. Their transformed bivectors remain in
the actual native ideal, and their initial classes scale by the determinant.
Consequently every special-linear row change fixes these normal coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K ι : Type*) [CommRing K]

-- Resolve the canonical structure at an abstract coefficient ring, before the
-- polynomial scalar type introduces additional typeclass-search branches.
private abbrev paperPluckerNormalModule {R : Type*} [CommRing R] (I : Ideal R) :
    Module R (PaperIdealAssociatedGraded I) := inferInstance

private abbrev paperPluckerNormalSMul {R : Type*} [CommRing R] (I : Ideal R) :
    SMul R (PaperIdealAssociatedGraded I) := inferInstance

local instance : Module (MvPolynomial (ι ⊕ ι) K)
    (PaperIdealAssociatedGraded (paperPluckerIdeal K ι)) :=
  paperPluckerNormalModule _

local instance : SMul (MvPolynomial (ι ⊕ ι) K)
    (PaperIdealAssociatedGraded (paperPluckerIdeal K ι)) :=
  paperPluckerNormalSMul _

/-- Native bivectors after a two-row transformation with arbitrary polynomial entries. -/
def paperPluckerRowActionGenerator (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K))
    (ij : ι × ι) : MvPolynomial (ι ⊕ ι) K :=
  Nieto1810.decomposableBivector
    (Nieto1810.twoRowAction S (fun i => X (Sum.inl i)) (fun i => X (Sum.inr i)) 0)
    (Nieto1810.twoRowAction S (fun i => X (Sum.inl i)) (fun i => X (Sum.inr i)) 1) ij.1 ij.2

/-- The native determinant covariance holds for polynomial-dependent row changes. -/
theorem paperPluckerRowActionGenerator_eq_det_mul
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K)) (ij : ι × ι) :
    paperPluckerRowActionGenerator K ι S ij = S.det * paperPluckerGenerator K ι ij :=
  Nieto1810.decomposableBivector_twoRowAction S _ _ ij.1 ij.2

/-- Every transformed bivector belongs to the actual original bivector ideal. -/
theorem paperPluckerRowActionGenerator_mem
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K)) (ij : ι × ι) :
    paperPluckerRowActionGenerator K ι S ij ∈ paperPluckerIdeal K ι := by
  rw [paperPluckerRowActionGenerator_eq_det_mul]
  exact Ideal.mul_mem_left _ _ (paperHomogeneousGeneratorIdeal_mem (paperPluckerGenerator K ι) ij)

/-- The actual initial class of a transformed native bivector. -/
def paperPluckerRowActionInitial
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K)) (i j : ι) :
    PaperIdealAssociatedGraded (paperPluckerIdeal K ι) :=
  paperNativeReesInitialLinearMap (paperPluckerIdeal K ι) 1
    ⟨paperPluckerRowActionGenerator K ι S (i, j), by
      simpa only [pow_one] using paperPluckerRowActionGenerator_mem K ι S (i, j)⟩

/-- Determinant covariance survives specialization into the actual normal ring. -/
theorem paperPluckerRowActionInitial_eq_det_smul
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K)) (i j : ι) :
    paperPluckerRowActionInitial K ι S i j =
      (S.det • paperPluckerNormalCoordinate K ι i j :
        PaperIdealAssociatedGraded (paperPluckerIdeal K ι)) := by
  let a : ((paperPluckerIdeal K ι) ^ 1 : Ideal (MvPolynomial (ι ⊕ ι) K)) :=
    ⟨paperPluckerGenerator K ι (i, j), by
      simpa only [pow_one, paperPluckerIdeal] using
        paperHomogeneousGeneratorIdeal_mem (paperPluckerGenerator K ι) (i, j)⟩
  have heq : (⟨paperPluckerRowActionGenerator K ι S (i, j), by
      simpa only [pow_one] using paperPluckerRowActionGenerator_mem K ι S (i, j)⟩ :
        ((paperPluckerIdeal K ι) ^ 1 : Ideal (MvPolynomial (ι ⊕ ι) K))) = S.det • a := by
    apply Subtype.ext
    exact paperPluckerRowActionGenerator_eq_det_mul K ι S (i, j)
  rw [paperPluckerRowActionInitial, heq, map_smul]
  rw [paperPluckerNormalCoordinate_eq_initial]
  rfl

/-- Every polynomial special-linear row change fixes the actual normal bivector coordinates. -/
theorem paperPluckerRowActionInitial_specialLinear
    (S : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial (ι ⊕ ι) K)) (i j : ι) :
    paperPluckerRowActionInitial K ι (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (ι ⊕ ι) K)) i j =
      paperPluckerNormalCoordinate K ι i j := by
  rw [paperPluckerRowActionInitial_eq_det_smul, S.det_coe, one_smul]

end

end GaloisForLFunctions.HTGeometry
