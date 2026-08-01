import GaloisForLFunctions.HTGeometry.FreeCoordinateField

/-!
# A free coordinate system presents its field as a free rational coordinate field

An algebraically independent family evaluates injectively on polynomials, hence on the fraction
field; if it also generates, the evaluation is an isomorphism.  So an algebraically independent
generating family identifies its field with the free rational coordinate field on its index.

This is the standard way a change of coordinates is used: transport a statement about coordinate
derivations along the identification.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {L E ι : Type*} [Field L] [Field E] [Algebra L E]

/-- Polynomial evaluation at a family. -/
def freeCoordinateBasisEvalPoly (s : ι → E) : MvPolynomial ι L →ₐ[L] E :=
  MvPolynomial.aeval s

theorem freeCoordinateBasisEvalPoly_injective {s : ι → E} (hs : AlgebraicIndependent L s) :
    Function.Injective (freeCoordinateBasisEvalPoly (L := L) s) := hs

/-- Evaluation of the free rational coordinate field at an algebraically independent family. -/
def freeCoordinateBasisEval {s : ι → E} (hs : AlgebraicIndependent L s) :
    FreeCoordinateRationalField L ι →ₐ[L] E :=
  { IsFractionRing.lift (freeCoordinateBasisEvalPoly_injective hs) with
    commutes' := fun c => by
      show IsFractionRing.lift (freeCoordinateBasisEvalPoly_injective hs)
        (algebraMap L (FreeCoordinateRationalField L ι) c) = _
      rw [IsScalarTower.algebraMap_apply L (MvPolynomial ι L) (FreeCoordinateRationalField L ι),
        IsFractionRing.lift_algebraMap]
      exact (freeCoordinateBasisEvalPoly (L := L) s).commutes c }

@[simp]
theorem freeCoordinateBasisEval_algebraMap {s : ι → E} (hs : AlgebraicIndependent L s)
    (p : MvPolynomial ι L) :
    freeCoordinateBasisEval hs
        (algebraMap (MvPolynomial ι L) (FreeCoordinateRationalField L ι) p) =
      freeCoordinateBasisEvalPoly (L := L) s p :=
  IsFractionRing.lift_algebraMap (freeCoordinateBasisEvalPoly_injective hs) p

@[simp]
theorem freeCoordinateBasisEval_freeCoordinate {s : ι → E} (hs : AlgebraicIndependent L s)
    (i : ι) : freeCoordinateBasisEval hs (freeCoordinate L ι i) = s i := by
  rw [freeCoordinate, freeCoordinateBasisEval_algebraMap, freeCoordinateBasisEvalPoly,
    MvPolynomial.aeval_X]

theorem freeCoordinateBasisEval_injective {s : ι → E} (hs : AlgebraicIndependent L s) :
    Function.Injective (freeCoordinateBasisEval hs) :=
  (freeCoordinateBasisEval hs).toRingHom.injective

theorem freeCoordinateBasisEval_surjective {s : ι → E} (hs : AlgebraicIndependent L s)
    (hgen : IntermediateField.adjoin L (Set.range s) = ⊤) :
    Function.Surjective (freeCoordinateBasisEval hs) := by
  have hrange : (freeCoordinateBasisEval hs).fieldRange = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact ⟨freeCoordinate L ι i, freeCoordinateBasisEval_freeCoordinate hs i⟩
  intro y
  have hy : y ∈ (freeCoordinateBasisEval hs).fieldRange := by
    rw [hrange]
    exact IntermediateField.mem_top
  exact hy

/-- **A free coordinate system presents its field.**  An algebraically independent generating family
identifies the free rational coordinate field on its index with the field it generates. -/
def freeCoordinateBasisEquiv {s : ι → E} (hs : AlgebraicIndependent L s)
    (hgen : IntermediateField.adjoin L (Set.range s) = ⊤) :
    FreeCoordinateRationalField L ι ≃ₐ[L] E :=
  AlgEquiv.ofBijective (freeCoordinateBasisEval hs)
    ⟨freeCoordinateBasisEval_injective hs, freeCoordinateBasisEval_surjective hs hgen⟩

@[simp]
theorem freeCoordinateBasisEquiv_freeCoordinate {s : ι → E} (hs : AlgebraicIndependent L s)
    (hgen : IntermediateField.adjoin L (Set.range s) = ⊤) (i : ι) :
    freeCoordinateBasisEquiv hs hgen (freeCoordinate L ι i) = s i :=
  freeCoordinateBasisEval_freeCoordinate hs i

end

end GaloisForLFunctions.HTGeometry
