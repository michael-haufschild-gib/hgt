import GaloisForLFunctions.HTGeometry.PaperHomogeneousNormalRelations
import GaloisForLFunctions.HTGeometry.PaperGenericMinorWeights

/-!
# Exact normal-coordinate relations for all generic matrix minors

Apply the source Rees coefficient kernel and weight bound to the complete
family of positive-size minors of a possibly infinite rectangular matrix
of variables. Every polynomial relation between the actual determinants is
preserved, and no new scalar relation appears among their initial classes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

noncomputable section

variable (K : Type*) [CommRing K] (ι κ : Type*)

/-- Fully paid presentation data for every minor of the native generic matrix ideal. -/
def paperGenericMinorNormalPresentation (r : ℕ) :
    PaperHomogeneousNormalPresentationData K (ι × κ)
      ((Fin (r + 1) → ι) × (Fin (r + 1) → κ))
      (deningerMatrixMinorIdeal (r + 1) (Matrix.mvPolynomialX ι κ K)) where
  generator p := ((Matrix.mvPolynomialX ι κ K).submatrix p.1 p.2).det
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem p := deningerMatrixMinorDet_mem _ _ p.1 p.2
  homogeneous p := paperVariableMinor_homogeneous K _ p.1 p.2
  order_bound := paperVariableMinorIdeal_weightOrder K ι κ (r + 1)

/-- Polynomial substitution into all actual generic-minor initial classes. -/
def paperGenericMinorNormalMap (r : ℕ) :
    MvPolynomial ((Fin (r + 1) → ι) × (Fin (r + 1) → κ)) K →+*
      PaperIdealAssociatedGraded (deningerMatrixMinorIdeal (r + 1) (Matrix.mvPolynomialX ι κ K)) :=
  (paperGenericMinorNormalPresentation K ι κ r).polynomialMap

/-- All scalar relations among generic minor initial classes are exactly the determinant relations. -/
theorem paperGenericMinorNormalMap_relations_iff (r : ℕ)
    (p : MvPolynomial ((Fin (r + 1) → ι) × (Fin (r + 1) → κ)) K) :
    paperGenericMinorNormalMap K ι κ r p = 0 ↔
      MvPolynomial.aeval (fun s : (Fin (r + 1) → ι) × (Fin (r + 1) → κ) =>
        ((Matrix.mvPolynomialX ι κ K).submatrix s.1 s.2).det) p = 0 :=
  (paperGenericMinorNormalPresentation K ι κ r).polynomialMap_eq_zero_iff p

/-- Exact equality of the complete ordinary and normal-coordinate relation ideals. -/
theorem paperGenericMinorNormalMap_kernel (r : ℕ) :
    RingHom.ker (paperGenericMinorNormalMap K ι κ r) =
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → ι) × (Fin (r + 1) → κ) =>
          ((Matrix.mvPolynomialX ι κ K).submatrix s.1 s.2).det)).toRingHom :=
  (paperGenericMinorNormalPresentation K ι κ r).kernel_eq

/-- Each coordinate is the initial class of its actual selected matrix determinant. -/
theorem paperGenericMinorNormalMap_X (r : ℕ)
    (s : (Fin (r + 1) → ι) × (Fin (r + 1) → κ)) :
    paperGenericMinorNormalMap K ι κ r (MvPolynomial.X s) =
      paperNativeReesSpecialization (deningerMatrixMinorIdeal (r + 1) (Matrix.mvPolynomialX ι κ K))
        (ReesGrading.mono _ 1 (((Matrix.mvPolynomialX ι κ K).submatrix s.1 s.2).det)
          (by simpa only [pow_one] using (deningerMatrixMinorDet_mem (r + 1)
            (Matrix.mvPolynomialX ι κ K) s.1 s.2))) :=
  (paperGenericMinorNormalPresentation K ι κ r).polynomialMap_X s

/-- The coordinate ring of the complete generic-minor family maps into the native normal cone. -/
def paperGenericMinorRelationQuotientMap (r : ℕ) :
    (MvPolynomial ((Fin (r + 1) → ι) × (Fin (r + 1) → κ)) K ⧸
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → ι) × (Fin (r + 1) → κ) =>
          ((Matrix.mvPolynomialX ι κ K).submatrix s.1 s.2).det)).toRingHom) →+*
      PaperIdealAssociatedGraded (deningerMatrixMinorIdeal (r + 1) (Matrix.mvPolynomialX ι κ K)) :=
  (paperGenericMinorNormalPresentation K ι κ r).relationQuotientMap

/-- The entire generic-minor coordinate ring, including its relations, survives injectively. -/
theorem paperGenericMinorRelationQuotientMap_injective (r : ℕ) :
    Function.Injective (paperGenericMinorRelationQuotientMap K ι κ r) :=
  (paperGenericMinorNormalPresentation K ι κ r).relationQuotientMap_injective

/-- The actual subring of generic determinants embeds into the associated graded ring. -/
def paperGenericMinorGeneratorRingEmbedding (r : ℕ) :
    (MvPolynomial.aeval (R := K)
      (fun s : (Fin (r + 1) → ι) × (Fin (r + 1) → κ) =>
        ((Matrix.mvPolynomialX ι κ K).submatrix s.1 s.2).det)).toRingHom.range →+*
      PaperIdealAssociatedGraded (deningerMatrixMinorIdeal (r + 1) (Matrix.mvPolynomialX ι κ K)) :=
  (paperGenericMinorNormalPresentation K ι κ r).generatorRingEmbedding

/-- No nonzero element of the native generic determinant subring is lost. -/
theorem paperGenericMinorGeneratorRingEmbedding_injective (r : ℕ) :
    Function.Injective (paperGenericMinorGeneratorRingEmbedding K ι κ r) :=
  (paperGenericMinorNormalPresentation K ι κ r).generatorRingEmbedding_injective

end

end GaloisForLFunctions.HTGeometry
