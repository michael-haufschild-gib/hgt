import GaloisForLFunctions.RepresentationLifting.KTheory.FiniteAbelianVirtualRing

/-!
# Augmentation quotients of finite abelian virtual characters

The integral Fourier ring equivalence identifies every power of the dimension
augmentation ideal with its group-algebra counterpart. In particular the
first-order quotient is a square-zero extension by the additive character
group after scalar extension to the integers.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.GroupAlgebraFirstJet
variable (G : Type*) [CommGroup G] [Fintype G]

private abbrev characterAlgebraCommRing : CommRing (MonoidAlgebra ℤ (LinearCharacter G)) :=
  MonoidAlgebra.commRing

attribute [local instance] characterAlgebraCommRing

theorem finiteAbelianCharacterAlgebraEquiv_comap_augmentation :
    Ideal.comap (finiteAbelianCharacterAlgebraEquiv G).toRingEquiv.toRingHom
      (virtualRepresentationAugmentationIdeal G) = augmentationIdeal ℤ (LinearCharacter G) := by
  ext f
  change virtualRepresentationAugmentation G (finiteAbelianCharacterAlgebraHom G f) = 0 ↔
    augmentation ℤ (LinearCharacter G) f = 0
  rw [finiteAbelianCharacterAlgebraHom_augmentation]

theorem finiteAbelianCharacterAlgebraEquiv_map_augmentation :
    Ideal.map (finiteAbelianCharacterAlgebraEquiv G).toRingEquiv.toRingHom
      (augmentationIdeal ℤ (LinearCharacter G)) = virtualRepresentationAugmentationIdeal G := by
  rw [← finiteAbelianCharacterAlgebraEquiv_comap_augmentation]
  exact Ideal.map_comap_of_surjective _ (finiteAbelianCharacterAlgebraEquiv G).surjective _

/-- Every ordinary dimension-augmentation quotient is an actual character-group algebra quotient. -/
def finiteAbelianVirtualAugmentationQuotient (n : ℕ) :
    (VirtualRepresentationRing G ⧸ (virtualRepresentationAugmentationIdeal G) ^ n) ≃ₐ[ℤ]
      (MonoidAlgebra ℤ (LinearCharacter G) ⧸ (augmentationIdeal ℤ (LinearCharacter G)) ^ n) :=
  (Ideal.quotientEquivAlg (R₁ := ℤ) (A := MonoidAlgebra ℤ (LinearCharacter G))
    (B := VirtualRepresentationRing G) ((augmentationIdeal ℤ (LinearCharacter G)) ^ n)
    ((virtualRepresentationAugmentationIdeal G) ^ n) (finiteAbelianCharacterAlgebraEquiv G)
    (by
      rw [Ideal.map_pow]
      exact congrArg (fun I : Ideal (VirtualRepresentationRing G) => I ^ n)
        (finiteAbelianCharacterAlgebraEquiv_map_augmentation G).symm)).symm

/-- The first-order quotient retains the character group as a square-zero moment. -/
def finiteAbelianVirtualFirstJet :
    (VirtualRepresentationRing G ⧸ (virtualRepresentationAugmentationIdeal G) ^ 2) ≃ₐ[ℤ]
      TrivSqZeroExt ℤ (MomentSpace ℤ (LinearCharacter G)) :=
  (finiteAbelianVirtualAugmentationQuotient G 2).trans (quotientEquiv ℤ (LinearCharacter G))

end GaloisForLFunctions.RepresentationLifting
