import GaloisForLFunctions.HTGeometry.PaperHomogeneousNormalRelations
import GaloisForLFunctions.RHTower.Deninger.DeningerHankelGlobalSecantPrime

/-!
# The complete Hankel-minor relation ring survives in normal coordinates

The paper's Rees kernel and weight bound apply to every minor of the native
countably indexed moment Hankel matrix at once. Scalar polynomial relations
are exactly preserved, over any commutative coefficient ring and at every rank.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

noncomputable section

variable (K : Type*) [CommRing K]

/-- Fully paid normal-presentation data for all native generic Hankel minors. -/
def paperHankelNormalPresentation (r : ℕ) :
    PaperHomogeneousNormalPresentationData K ℕ
      ((Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ)) (deningerGenericHankelIdeal K r) where
  generator p := ((deningerGenericMomentHankel K).submatrix p.1 p.2).det
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem p := deningerMatrixMinorDet_mem _ _ p.1 p.2
  homogeneous p := deningerGenericHankelMinor_isHomogeneous K r p.1 p.2
  order_bound := by
    rw [deningerGenericHankelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
    rintro p ⟨rows, cols, rfl⟩
    exact paperWeightOrderIdeal_mem_of_homogeneous _ _
      (paperIsWeightedHomogeneous_int (deningerGenericHankelMinor_isHomogeneous K r rows cols))

/-- Simultaneous substitution into every Hankel-minor initial class of the actual rank ideal. -/
def paperHankelNormalMap (r : ℕ) :
    MvPolynomial ((Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ)) K →+*
      PaperIdealAssociatedGraded (deningerGenericHankelIdeal K r) :=
  (paperHankelNormalPresentation K r).polynomialMap

/-- Exact preservation of every polynomial relation among the actual Hankel minors. -/
theorem paperHankelNormalMap_relations_iff (r : ℕ)
    (p : MvPolynomial ((Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ)) K) :
    paperHankelNormalMap K r p = 0 ↔
      MvPolynomial.aeval (fun s : (Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ) =>
        ((deningerGenericMomentHankel K).submatrix s.1 s.2).det) p = 0 :=
  (paperHankelNormalPresentation K r).polynomialMap_eq_zero_iff p

/-- The ordinary Hankel relation ideal equals the normal-coordinate relation ideal. -/
theorem paperHankelNormalMap_kernel (r : ℕ) :
    RingHom.ker (paperHankelNormalMap K r) =
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ) =>
          ((deningerGenericMomentHankel K).submatrix s.1 s.2).det)).toRingHom :=
  (paperHankelNormalPresentation K r).kernel_eq

/-- Every normal coordinate is represented by its exact native Hankel determinant. -/
theorem paperHankelNormalMap_X (r : ℕ)
    (s : (Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ)) :
    paperHankelNormalMap K r (MvPolynomial.X s) =
      paperNativeReesSpecialization (deningerGenericHankelIdeal K r)
        (ReesGrading.mono _ 1 (((deningerGenericMomentHankel K).submatrix s.1 s.2).det)
          (by simpa only [pow_one, deningerGenericHankelIdeal] using (deningerMatrixMinorDet_mem (r + 1)
            (deningerGenericMomentHankel K) s.1 s.2))) :=
  (paperHankelNormalPresentation K r).polynomialMap_X s

/-- The full coordinate ring of the native Hankel-minor family maps into its normal cone. -/
def paperHankelRelationQuotientMap (r : ℕ) :
    (MvPolynomial ((Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ)) K ⧸
      RingHom.ker (MvPolynomial.aeval (R := K)
        (fun s : (Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ) =>
          ((deningerGenericMomentHankel K).submatrix s.1 s.2).det)).toRingHom) →+*
      PaperIdealAssociatedGraded (deningerGenericHankelIdeal K r) :=
  (paperHankelNormalPresentation K r).relationQuotientMap

/-- Every nonzero Hankel generator-ring class survives the normal-cone embedding. -/
theorem paperHankelRelationQuotientMap_injective (r : ℕ) :
    Function.Injective (paperHankelRelationQuotientMap K r) :=
  (paperHankelNormalPresentation K r).relationQuotientMap_injective

/-- The actual countable Hankel-minor subring embeds into the native associated graded ring. -/
def paperHankelGeneratorRingEmbedding (r : ℕ) :
    (MvPolynomial.aeval (R := K)
      (fun s : (Fin (r + 1) → ℕ) × (Fin (r + 1) → ℕ) =>
        ((deningerGenericMomentHankel K).submatrix s.1 s.2).det)).toRingHom.range →+*
      PaperIdealAssociatedGraded (deningerGenericHankelIdeal K r) :=
  (paperHankelNormalPresentation K r).generatorRingEmbedding

/-- The complete native Hankel determinant subring loses no elements in normal coordinates. -/
theorem paperHankelGeneratorRingEmbedding_injective (r : ℕ) :
    Function.Injective (paperHankelGeneratorRingEmbedding K r) :=
  (paperHankelNormalPresentation K r).generatorRingEmbedding_injective

end

end GaloisForLFunctions.HTGeometry
