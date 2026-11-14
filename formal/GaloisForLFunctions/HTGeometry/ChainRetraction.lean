import GaloisForLFunctions.HTGeometry.FamilySimplicialSet

/-!
# Lifting a chain along an injection of simplices

The chains of a simplicial set are a coproduct of copies of the coefficients, one for each simplex,
so a partial map on simplices — a choice, for some simplices of the target, of a simplex of the
source mapping to it — retracts the chains.  A chain carried by simplices in the image is then the
image of an explicit chain of the source, with no membership proof carried inside the sum.

This is what puts the two halves of a Mayer--Vietoris splitting where they belong: a chain of the
whole complex supported on the base is a chain of the base, and one supported on a single piece is
a chain of the disjoint union of the pieces.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite

universe v u c

section

variable {C : Type c} [Category.{v} C] [Preadditive C] [Limits.HasCoproducts.{u} C]
variable {Y Z : SSet.{u}} (n : ℕ) (R : C) (r : Y _⦋n⦌ → Option (Z _⦋n⦌))

/-- The retraction of the chains attached to a partial choice of preimages. -/
noncomputable def chainRetraction : (Y.chainComplex R).X n ⟶ (Z.chainComplex R).X n :=
  (Y.isColimitChainComplexXCofan R n).desc (Cofan.mk _ fun y =>
    match r y with
    | none => 0
    | some z => Z.ιChainComplex (R := R) z)

theorem ι_chainRetraction_of_eq {y : Y _⦋n⦌} {z : Z _⦋n⦌} (h : r y = some z) :
    Y.ιChainComplex (R := R) y ≫ chainRetraction n R r = Z.ιChainComplex (R := R) z := by
  refine ((Y.isColimitChainComplexXCofan R n).fac _ ⟨y⟩).trans ?_
  show (match r y with
    | none => 0
    | some z => Z.ιChainComplex (R := R) z) = Z.ιChainComplex (R := R) z
  rw [h]

/-- **A chain of the source is recovered from its image** at every simplex the choice covers. -/
theorem ι_chainRetraction_comp {incl : Z ⟶ Y}
    (hr : ∀ (y : Y _⦋n⦌) (z : Z _⦋n⦌), r y = some z → incl.app (op ⦋n⦌) z = y)
    {y : Y _⦋n⦌} {z : Z _⦋n⦌} (h : r y = some z) :
    Y.ιChainComplex (R := R) y ≫ chainRetraction n R r ≫ (SSet.chainComplexMap incl R).f n
      = Y.ιChainComplex (R := R) y := by
  rw [← Category.assoc, ι_chainRetraction_of_eq n R r h, SSet.ι_chainComplexMap_f, hr y z h]

end

end GaloisForLFunctions.HTGeometry
