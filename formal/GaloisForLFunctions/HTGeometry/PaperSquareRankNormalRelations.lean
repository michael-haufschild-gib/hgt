import GaloisForLFunctions.HTGeometry.PaperGenericMinorNormalRelations
import GaloisForLFunctions.HTGeometry.GenericDeterminantalSmooth

/-!
# Full relation preservation for the native square-matrix rank ideal

Apply the source Rees kernel directly to `detIdeal (genericVarMatrix K N)`.
The complete determinant generator ring, with all its scalar polynomial
relations, embeds in the associated graded ring over every coefficient ring.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type*) [CommRing K]

/-- Fully paid presentation data in the native square-rank ideal interface. -/
def paperSquareRankNormalPresentation (N r : ℕ) :
    PaperHomogeneousNormalPresentationData K (Fin N × Fin N)
      ((Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N))
      (detIdeal (genericVarMatrix K N) (r + 1)) where
  generator s := ((genericVarMatrix K N).submatrix s.1 s.2).det
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem s := minor_mem_detIdeal _ s.1 s.2
  homogeneous s := paperVariableMinor_homogeneous K _ s.1 s.2
  order_bound := by
    apply detIdeal_le
    intro rows cols
    exact paperWeightOrderIdeal_mem_of_homogeneous _ _
      (paperIsWeightedHomogeneous_int (paperVariableMinor_homogeneous K (r + 1) rows cols))

/-- All square-rank determinant initial classes evaluated simultaneously. -/
def paperSquareRankNormalMap (N r : ℕ) :
    MvPolynomial ((Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N)) K →+*
      PaperIdealAssociatedGraded (detIdeal (genericVarMatrix K N) (r + 1)) :=
  (paperSquareRankNormalPresentation K N r).polynomialMap

/-- The native square-rank initial classes retain exactly the actual determinant relations. -/
theorem paperSquareRankNormalMap_relations_iff (N r : ℕ)
    (p : MvPolynomial ((Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N)) K) :
    paperSquareRankNormalMap K N r p = 0 ↔
      MvPolynomial.aeval (fun s : (Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N) =>
        ((genericVarMatrix K N).submatrix s.1 s.2).det) p = 0 :=
  (paperSquareRankNormalPresentation K N r).polynomialMap_eq_zero_iff p

/-- Equality of ordinary and normal relation ideals in the native rank geometry. -/
theorem paperSquareRankNormalMap_kernel (N r : ℕ) :
    RingHom.ker (paperSquareRankNormalMap K N r) =
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N) =>
          ((genericVarMatrix K N).submatrix s.1 s.2).det)).toRingHom :=
  (paperSquareRankNormalPresentation K N r).kernel_eq

/-- Each normal coordinate has exactly its native square-matrix determinant representative. -/
theorem paperSquareRankNormalMap_X (N r : ℕ)
    (s : (Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N)) :
    paperSquareRankNormalMap K N r (MvPolynomial.X s) =
      paperNativeReesSpecialization (detIdeal (genericVarMatrix K N) (r + 1))
        (ReesGrading.mono _ 1 (((genericVarMatrix K N).submatrix s.1 s.2).det)
          (by simpa only [pow_one] using (minor_mem_detIdeal (genericVarMatrix K N) s.1 s.2))) :=
  (paperSquareRankNormalPresentation K N r).polynomialMap_X s

/-- The native square-rank determinant coordinate ring maps into its normal cone ring. -/
def paperSquareRankRelationQuotientMap (N r : ℕ) :
    (MvPolynomial ((Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N)) K ⧸
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N) =>
          ((genericVarMatrix K N).submatrix s.1 s.2).det)).toRingHom) →+*
      PaperIdealAssociatedGraded (detIdeal (genericVarMatrix K N) (r + 1)) :=
  (paperSquareRankNormalPresentation K N r).relationQuotientMap

/-- The entire original determinant relation quotient survives injectively in native rank geometry. -/
theorem paperSquareRankRelationQuotientMap_injective (N r : ℕ) :
    Function.Injective (paperSquareRankRelationQuotientMap K N r) :=
  (paperSquareRankNormalPresentation K N r).relationQuotientMap_injective

/-- The actual native square-rank determinant subring embeds in its associated graded ring. -/
def paperSquareRankGeneratorRingEmbedding (N r : ℕ) :
    (MvPolynomial.aeval (R := K)
      (fun s : (Fin (r + 1) → Fin N) × (Fin (r + 1) → Fin N) =>
        ((genericVarMatrix K N).submatrix s.1 s.2).det)).toRingHom.range →+*
      PaperIdealAssociatedGraded (detIdeal (genericVarMatrix K N) (r + 1)) :=
  (paperSquareRankNormalPresentation K N r).generatorRingEmbedding

/-- No element of the full native square-rank generator subring is collapsed. -/
theorem paperSquareRankGeneratorRingEmbedding_injective (N r : ℕ) :
    Function.Injective (paperSquareRankGeneratorRingEmbedding K N r) :=
  (paperSquareRankNormalPresentation K N r).generatorRingEmbedding_injective

end

end GaloisForLFunctions.HTGeometry
