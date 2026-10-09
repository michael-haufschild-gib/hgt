import GaloisForLFunctions.HTGeometry.PaperSymmetricPairGenerators
import GaloisForLFunctions.HTGeometry.PaperHomogeneousGeneratorIdeal

/-!
# A full polynomial normal space for the native symmetric pair

Apply the proven OpenAI StableCoordinate Rees coefficient kernel to the native
three-coefficient symmetric pair. Its actual initial classes generate a polynomial
ring in three variables over any commutative coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K]

/-- Ideal of the three native universal symmetric-pair coefficients. -/
def paperSymmetricPairIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  paperHomogeneousGeneratorIdeal (paperSymmetricPairGenerator K)

/-- Every source order and homogeneity requirement is proved for the actual native ideal. -/
def paperSymmetricPairNormalPresentation :
    PaperHomogeneousNormalPresentationData K (Fin 4) (Fin 3) (paperSymmetricPairIdeal K) :=
  paperHomogeneousGeneratorNormalPresentation (paperSymmetricPairGenerator K) 2
    (Nat.succ_pos 1) (paperSymmetricPairGenerator_homogeneous K)

/-- The actual normal-coordinate map of the native symmetric-pair family. -/
def paperSymmetricPairNormalMap :
    MvPolynomial (Fin 3) K →+* PaperIdealAssociatedGraded (paperSymmetricPairIdeal K) :=
  (paperSymmetricPairNormalPresentation K).polynomialMap

/-- Source specialization preserves precisely the original polynomial relations. -/
theorem paperSymmetricPairNormalMap_relations_iff (p : MvPolynomial (Fin 3) K) :
    paperSymmetricPairNormalMap K p = 0 ↔ aeval (paperSymmetricPairGenerator K) p = 0 :=
  (paperSymmetricPairNormalPresentation K).polynomialMap_eq_zero_iff p

/-- The actual initial classes satisfy no nonzero scalar polynomial relation. -/
theorem paperSymmetricPairNormalMap_eq_zero_iff (p : MvPolynomial (Fin 3) K) :
    paperSymmetricPairNormalMap K p = 0 ↔ p = 0 := by
  rw [paperSymmetricPairNormalMap_relations_iff]
  exact (paperSymmetricPairSubstitution_injective K).eq_iff' (map_zero _)

/-- Three polynomially independent actual normal coordinates, in every characteristic. -/
theorem paperSymmetricPairNormalMap_injective :
    Function.Injective (paperSymmetricPairNormalMap K) := by
  intro p q h
  apply sub_eq_zero.mp
  apply (paperSymmetricPairNormalMap_eq_zero_iff K (p - q)).mp
  rw [map_sub, h, sub_self]

/-- Each polynomial variable maps to the actual native generator's initial class. -/
theorem paperSymmetricPairNormalMap_X (i : Fin 3) :
    paperSymmetricPairNormalMap K (X i) =
      paperNativeReesSpecialization (paperSymmetricPairIdeal K)
        (ReesGrading.mono (paperSymmetricPairIdeal K) 1 (paperSymmetricPairGenerator K i) (by
          simpa only [pow_one, paperSymmetricPairIdeal] using
            paperHomogeneousGeneratorIdeal_mem (paperSymmetricPairGenerator K) i)) :=
  (paperSymmetricPairNormalPresentation K).polynomialMap_X i

end

end GaloisForLFunctions.HTGeometry
