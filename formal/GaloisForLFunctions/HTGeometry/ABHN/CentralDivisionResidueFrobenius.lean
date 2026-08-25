import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalDegreeExact
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Cyclic Frobenius structure of determinant residue fields

The determinant residue division ring of a local central division algebra is finite, hence a
field by Wedderburn.  Its extension of the finite base residue field is therefore Galois with
cyclic automorphism group.  Exact local residue degree identifies the order of this cyclic group
with `deg(A)`.

This supplies the complete residue-side Frobenius datum.  Lifting its generator to the
residue-exhausting maximal subfield is the next local cyclic-exhaustion step.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- Local compactness supplies the finite base-residue instance used by finite-field Galois
theory. -/
noncomputable instance normValuationResidueFinite_of_locallyCompact :
    Finite (NormValuationResidue (F := F)) :=
  normValuationResidue_finite (F := F)

omit [Algebra.IsCentral F A] in
/-- The determinant residue extension of a local central division algebra is Galois. -/
theorem divisionAlgebraDeterminantResidue_isGalois :
    IsGalois (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  infer_instance

omit [Algebra.IsCentral F A] in
/-- The determinant residue Galois group is cyclic. -/
theorem divisionAlgebraDeterminantResidue_galoisGroup_isCyclic :
    IsCyclic Gal(DivisionAlgebraDeterminantResidue (F := F) (A := A) /
      NormValuationResidue (F := F)) := by
  infer_instance

/-- The cyclic determinant residue Galois group has order equal to the division-algebra degree. -/
theorem divisionAlgebraDeterminantResidue_galoisGroup_natCard_eq_degree :
    Nat.card Gal(DivisionAlgebraDeterminantResidue (F := F) (A := A) /
        NormValuationResidue (F := F)) =
      divisionAlgebraDegree (F := F) (A := A) := by
  letI : IsGalois (NormValuationResidue (F := F))
      (DivisionAlgebraDeterminantResidue (F := F) (A := A)) :=
    divisionAlgebraDeterminantResidue_isGalois (F := F) (A := A)
  rw [IsGalois.card_aut_eq_finrank]
  exact finrank_divisionAlgebraDeterminantResidue_eq_degree (F := F) (A := A)

/-- A chosen generator of the cyclic determinant-residue Galois group.  This is intentionally not
yet named arithmetic Frobenius: identifying the canonical finite-field power map with this chosen
generator is a separate orientation theorem. -/
noncomputable def divisionAlgebraDeterminantResidueCyclicGenerator :
    Gal(DivisionAlgebraDeterminantResidue (F := F) (A := A) /
      NormValuationResidue (F := F)) :=
  (divisionAlgebraDeterminantResidue_galoisGroup_isCyclic
    (F := F) (A := A)).exists_generator.choose

omit [Algebra.IsCentral F A] in
/-- Every determinant-residue Galois automorphism is a power of the chosen cyclic generator. -/
theorem divisionAlgebraDeterminantResidueCyclicGenerator_exists_zpow
    (σ : Gal(DivisionAlgebraDeterminantResidue (F := F) (A := A) /
      NormValuationResidue (F := F))) :
    σ ∈ Subgroup.zpowers
      (divisionAlgebraDeterminantResidueCyclicGenerator (F := F) (A := A)) :=
  (divisionAlgebraDeterminantResidue_galoisGroup_isCyclic
    (F := F) (A := A)).exists_generator.choose_spec σ

/-- Finite-level cyclic coordinate on the determinant-residue Galois group. -/
noncomputable def divisionAlgebraDeterminantResidueGaloisZModEquiv :
    Multiplicative (ZMod (divisionAlgebraDegree (F := F) (A := A))) ≃*
      Gal(DivisionAlgebraDeterminantResidue (F := F) (A := A) /
        NormValuationResidue (F := F)) :=
  zmodMulEquivOfGenerator
    (divisionAlgebraDeterminantResidueCyclicGenerator_exists_zpow (F := F) (A := A))
    (divisionAlgebraDeterminantResidue_galoisGroup_natCard_eq_degree (F := F) (A := A))

end

end GaloisForLFunctions.HTGeometry.ABHN
