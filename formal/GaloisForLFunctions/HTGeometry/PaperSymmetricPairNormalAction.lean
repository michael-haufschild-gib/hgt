import GaloisForLFunctions.HTGeometry.PaperSymmetricPairNormalSpace
import GaloisForLFunctions.HTGeometry.PaperNativeReesInitialLinearMap
import GaloisForLFunctions.HTGeometry.PaperSymmetricPairNormalDiscriminant

/-!
# Symmetric-square covariance of the actual normal coordinates

The native intertwining identity descends to actual initial classes. Coordinate
changes may have polynomial entries; membership in the original ideal is proved.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Matrix
open scoped BigOperators

noncomputable section

variable (K : Type*) [CommRing K]

private abbrev paperSymmetricNormalModule {R : Type*} [CommRing R] (I : Ideal R) :
    Module R (PaperIdealAssociatedGraded I) := inferInstance

private abbrev paperSymmetricNormalSMul {R : Type*} [CommRing R] (I : Ideal R) :
    SMul R (PaperIdealAssociatedGraded I) := inferInstance

private abbrev paperSymmetricNormalAlgebra {R : Type*} [CommRing R] (I : Ideal R) :
    Algebra R (PaperIdealAssociatedGraded I) := inferInstance

local instance : Algebra (MvPolynomial (Fin 4) K)
    (PaperIdealAssociatedGraded (paperSymmetricPairIdeal K)) := paperSymmetricNormalAlgebra _

local instance : Module (MvPolynomial (Fin 4) K)
    (PaperIdealAssociatedGraded (paperSymmetricPairIdeal K)) := paperSymmetricNormalModule _

local instance : SMul (MvPolynomial (Fin 4) K)
    (PaperIdealAssociatedGraded (paperSymmetricPairIdeal K)) := paperSymmetricNormalSMul _

/-- Apply a polynomial matrix to both vectors before taking their native symmetric pair. -/
def paperSymmetricPairTransformedGenerator
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) : Fin 3 → MvPolynomial (Fin 4) K :=
  symmetricPair (S.mulVec ![X 0, X 1]) (S.mulVec ![X 2, X 3])

/-- The original native symmetric-square intertwining identity. -/
theorem paperSymmetricPairTransformedGenerator_eq
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) (i : Fin 3) :
    paperSymmetricPairTransformedGenerator K S i =
      ∑ j, symmetricSquareMatrix S i j * paperSymmetricPairGenerator K j :=
  congrFun (symmetricPair_mulVec S ![X 0, X 1] ![X 2, X 3]) i

/-- Each transformed coefficient belongs to the original native coefficient ideal. -/
theorem paperSymmetricPairTransformedGenerator_mem
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) (i : Fin 3) :
    paperSymmetricPairTransformedGenerator K S i ∈ paperSymmetricPairIdeal K := by
  rw [paperSymmetricPairTransformedGenerator_eq]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (paperHomogeneousGeneratorIdeal_mem (paperSymmetricPairGenerator K) j)

/-- The actual initial vector after a polynomial coordinate change. -/
def paperSymmetricPairNormalAction
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) (i : Fin 3) :
    PaperIdealAssociatedGraded (paperSymmetricPairIdeal K) :=
  paperNativeReesInitialLinearMap (paperSymmetricPairIdeal K) 1
    ⟨paperSymmetricPairTransformedGenerator K S i, by
      simpa only [pow_one] using paperSymmetricPairTransformedGenerator_mem K S i⟩

/-- The source initial-class map preserves the native symmetric-square covariance law. -/
theorem paperSymmetricPairNormalAction_covariance
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) (i : Fin 3) :
    paperSymmetricPairNormalAction K S i =
      ∑ j, symmetricSquareMatrix S i j • paperSymmetricPairNormalMap K (X j) := by
  let a : Fin 3 → ((paperSymmetricPairIdeal K) ^ 1 : Ideal (MvPolynomial (Fin 4) K)) :=
    fun j => ⟨paperSymmetricPairGenerator K j, by
      simpa only [pow_one, paperSymmetricPairIdeal] using
        paperHomogeneousGeneratorIdeal_mem (paperSymmetricPairGenerator K) j⟩
  have heq : (⟨paperSymmetricPairTransformedGenerator K S i, by
      simpa only [pow_one] using paperSymmetricPairTransformedGenerator_mem K S i⟩ :
        ((paperSymmetricPairIdeal K) ^ 1 : Ideal (MvPolynomial (Fin 4) K))) =
      ∑ j, symmetricSquareMatrix S i j • a j := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower, smul_eq_mul] using
      paperSymmetricPairTransformedGenerator_eq K S i
  rw [paperSymmetricPairNormalAction, heq, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, paperSymmetricPairNormalMap_X]
  rfl

/-- Polynomial coordinate changes scale the actual normal discriminant by determinant square. -/
theorem paperSymmetricPairNormalAction_discriminant
    (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K)) :
    paperSymmetricDiscriminant (paperSymmetricPairNormalAction K S) =
      (algebraMap (MvPolynomial (Fin 4) K)
        (PaperIdealAssociatedGraded (paperSymmetricPairIdeal K)) S.det) ^ 2 *
          paperSymmetricPairNormalDiscriminant K := by
  have hv := funext (paperSymmetricPairNormalAction_covariance K S)
  rw [hv]
  exact paperSymmetricDiscriminant_smul S (fun i => paperSymmetricPairNormalMap K (X i))

/-- Every polynomial special-linear coordinate change fixes the actual normal discriminant. -/
theorem paperSymmetricPairNormalAction_specialLinear_discriminant
    (S : Matrix.SpecialLinearGroup (Fin 2) (MvPolynomial (Fin 4) K)) :
    paperSymmetricDiscriminant
        (paperSymmetricPairNormalAction K (S : Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 4) K))) =
      paperSymmetricPairNormalDiscriminant K := by
  rw [paperSymmetricPairNormalAction_discriminant, S.det_coe, map_one, one_pow, one_mul]

end

end GaloisForLFunctions.HTGeometry
