import GaloisForLFunctions.HTGeometry.BuildingLowerLink

/-!
# Cutting an order complex at a maximal element

At a maximal element the star is the down-set below it, which has a greatest element and is therefore
contractible, and the punctured star is the lower link alone.  So the homology of the order complex
is controlled by the complement of that element together with the lower link.

For a building this is the cut at a hyperplane: the intersection term is the building of the
hyperplane, one dimension down, with no join to analyse.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial

universe v u

variable {P : Type u} [PartialOrder P]

/-- **Cutting an order complex at a maximal element.** -/
theorem isZero_homology_nerve_of_maximal (p : P) (hmax : ∀ q, p ≤ q → q = p)
    {C : Type u} [Category.{v} C] [Abelian C] [Limits.HasCoproducts.{u} C]
    (R : C) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) (hi : 1 ≤ i)
    (hcompl : Limits.IsZero (((nerveSubcomplex {q : P | q ≠ p} : SSet.{u})).homology R i))
    (hlower : Limits.IsZero (((nerveSubcomplex {q : P | q < p} : SSet.{u})).homology R j)) :
    Limits.IsZero (((nerve P).chainComplex R).homology i) := by
  refine isZero_homology_nerve_of_vertex p R i j hij hi hcompl ?_
  rw [generalStar_inter_compl_eq_of_maximal p hmax]
  exact hlower

variable {R : Type*} {M : Type u} [Ring R] [AddCommGroup M] [Module R M]

/-- The building of a module: its proper nonzero submodules. -/
def buildingPoset (R : Type*) (M : Type u) [Ring R] [AddCommGroup M] [Module R M] : Type u :=
  {U : Submodule R M // ⊥ < U ∧ U < ⊤}

instance : PartialOrder (buildingPoset R M) := Subtype.partialOrder _

/-- **A hyperplane is a maximal vertex of the building.** -/
theorem isMaximal_hyperplane {H : buildingPoset R M} (hH : ∀ U : Submodule R M, H.1 < U → U = ⊤)
    (U : buildingPoset R M) (h : H ≤ U) : U = H := by
  refine Subtype.ext ?_
  rcases eq_or_lt_of_le (show H.1 ≤ U.1 from h) with heq | hlt
  · exact heq.symm
  · exact absurd (hH U.1 hlt) (ne_of_lt U.2.2)

end GaloisForLFunctions.HTGeometry
