import GaloisForLFunctions.HTGeometry.PaperSegreNormalRelations

/-!
# The native Segre ring embeds in the pair-product normal cone

The source Rees specialization preserves exactly the native Segre presentation
kernel. Descent through that presentation embeds the existing diagonal ring,
with its actual balanced monomial coordinates, into the associated graded ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K] (m n : ℕ)

/-- The existing native Segre coordinate ring maps into the actual normal ring. -/
def paperSegreNormalEmbedding : SegreDiagonalRing K m n →+*
    PaperIdealAssociatedGraded (paperSegrePairIdeal K m n) :=
  RingHom.liftOfSurjective (segreDiagonalPresentation K m n).toRingHom
    (segreDiagonalPresentation_surjective K m n)
    ⟨paperSegreNormalMap K m n, by
      intro p hp
      exact (paperSegreNormalMap_eq_zero_iff K m n p).mpr hp⟩

/-- The embedding is induced by the actual generator initial-class map. -/
theorem paperSegreNormalEmbedding_presentation
    (p : MvPolynomial (Fin (m + 1) × Fin (n + 1)) K) :
    paperSegreNormalEmbedding K m n (segreDiagonalPresentation K m n p) =
      paperSegreNormalMap K m n p :=
  RingHom.liftOfSurjective_comp_apply _ _ _ p

/-- No element of the existing Segre coordinate ring is lost in the normal ring. -/
theorem paperSegreNormalEmbedding_injective :
    Function.Injective (paperSegreNormalEmbedding K m n) := by
  intro x y h
  obtain ⟨p, rfl⟩ := segreDiagonalPresentation_surjective K m n x
  obtain ⟨q, rfl⟩ := segreDiagonalPresentation_surjective K m n y
  rw [paperSegreNormalEmbedding_presentation, paperSegreNormalEmbedding_presentation] at h
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (paperSegreNormalMap_eq_zero_iff K m n (p - q)).mp
  rw [map_sub, h, sub_self]

/-- Native balanced pair monomials become initial classes of the actual Cox-ring products. -/
theorem paperSegreNormalEmbedding_pair (i : Fin (m + 1)) (j : Fin (n + 1)) :
    paperSegreNormalEmbedding K m n
        (AddMonoidAlgebra.single (segrePairExponent m n i j) 1) =
      paperNativeReesSpecialization (paperSegrePairIdeal K m n)
        (ReesGrading.mono (paperSegrePairIdeal K m n) 1
          (paperSegrePairGenerator K m n (i, j)) (by
            simpa only [pow_one, paperSegrePairIdeal] using
              paperHomogeneousGeneratorIdeal_mem (paperSegrePairGenerator K m n) (i, j))) := by
  rw [← paperSegreDiagonalPresentation_X, paperSegreNormalEmbedding_presentation]
  exact (paperSegreNormalPresentation K m n).polynomialMap_X (i, j)

end

end GaloisForLFunctions.HTGeometry
