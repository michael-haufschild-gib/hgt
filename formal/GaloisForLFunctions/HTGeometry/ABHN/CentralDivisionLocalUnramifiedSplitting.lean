import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfield
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionMaximalSubfieldScalarExtension

/-!
# Unramified splitting fields for local central division algebras

The full-residue-degree subfield built from the determinant residue generator is not merely of
the correct degree.  Comparing it with any maximal commutative subfield containing its generator
shows that the two coincide.  Existing double-centralizer machinery then proves that scalar
extension to this same residue-exhausting field splits the division algebra's Brauer class.

This closes the local splitting-field part of cyclic exhaustion.  The next mathematical bridge is
to lift residue Frobenius to this specific subfield and thereby identify it as cyclic Galois over
the base.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped IsMulCommutative

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F] [DivisionRing A] [Algebra F A]
  [Module.Finite F A] [Algebra.IsCentral F A]

/-- Every local central division algebra has one integral generator whose field has full degree,
has the full determinant residue field, is maximal commutative, and splits the Brauer class after
scalar extension. -/
theorem exists_residueExhausting_maximalSubfield_scalarExtension_eq_split :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          Nonempty
            (DivisionAlgebraDeterminantRestrictedResidue (F := F) (A := A) T hT ≃+*
              DivisionAlgebraDeterminantResidue (F := F) (A := A)) ∧
          (∀ U : Subalgebra F A, T ≤ U → IsMulCommutative U → U = T) ∧
          (letI : Field T := hT.toField
           scalarExtensionBrauerMap F T (brauerClass (centralDivisionCSA F A)) =
             brauerSplitClass T) := by
  obtain ⟨x, hT, hdegree, hequiv⟩ :=
    exists_maximalSubfield_restrictedResidue_equiv (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  have hcommT : IsMulCommutative T := inferInstance
  obtain ⟨S, hTS, hcommS, hfieldS, hmaxS⟩ :=
    exists_maximalCommutativeSubfield_containing_element F A (x : A)
  have hSsq : Module.finrank F S * Module.finrank F S = Module.finrank F A :=
    maximalCommutativeSubfield_finrank_sq F A S hcommS hfieldS hmaxS
  have hSdegree : Module.finrank F S = divisionAlgebraDegree (F := F) (A := A) :=
    Nat.mul_self_inj.mp
      (hSsq.trans (divisionAlgebraDegree_mul_self (F := F) (A := A)).symm)
  have hTeqS : T = S :=
    Subalgebra.eq_of_le_of_finrank_eq hTS (hdegree.trans hSdegree.symm)
  have hmaxT : ∀ U : Subalgebra F A, T ≤ U → IsMulCommutative U → U = T := by
    intro U hTU hcommU
    exact (hmaxS U (by simpa only [hTeqS] using hTU) hcommU).trans hTeqS.symm
  refine ⟨x, hT, hdegree, hequiv, hmaxT, ?_⟩
  exact scalarExtensionBrauerMap_centralDivisionCSA_eq_split_of_maximalSubfield
    F A T hcommT hT hmaxT

end

end GaloisForLFunctions.HTGeometry.ABHN
