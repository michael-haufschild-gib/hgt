import GaloisForLFunctions.HTGeometry.SimplicialMayerVietorisSup

/-!
# Folding a finite cover

A finite family of subcomplexes is folded one piece at a time: if every piece is acyclic in a degree
and every piece meets the union of the earlier ones acyclically one degree down, then the union of
the whole family is acyclic in that degree.

This is the many-piece cover that a Solomon--Tits argument needs, reduced to repeated use of the
two-piece Mayer--Vietoris over the union.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
variable {X : SSet.{w}} (R : C) {ι : Type*} (A : ι → X.Subcomplex)

/-- **A finite union of acyclic pieces with acyclic partial intersections is acyclic.** -/
theorem isZero_homology_finsetSup (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j)
    (hA : ∀ a, Limits.IsZero ((((A a : X.Subcomplex) : SSet.{w}).chainComplex R).homology i))
    (hint : ∀ (a : ι) (t : Finset ι),
      Limits.IsZero ((((A a ⊓ t.sup A : X.Subcomplex) : SSet.{w}).chainComplex R).homology j))
    {s : Finset ι} (hs : s.Nonempty) :
    Limits.IsZero ((((s.sup A : X.Subcomplex) : SSet.{w}).chainComplex R).homology i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      rw [Finset.sup_singleton]
      exact hA a
  | cons a t hat ht ih =>
      rw [Finset.sup_cons]
      exact isZero_homology_of_mayerVietoris_sup X R (A a) (t.sup A) i j hij (hA a) ih (hint a t)

end GaloisForLFunctions.HTGeometry
