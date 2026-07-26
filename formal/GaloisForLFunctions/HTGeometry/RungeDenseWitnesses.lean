import GaloisForLFunctions.HTGeometry.RungeOneAtomAbsorption

/-!
# Realizations of the Runge-dense generator interface

A generator whose adjoined subalgebra is already everything is Runge dense, since a subalgebra is
contained in its own topological closure.  This is the algebraic end of the interface: density is
needed only to close the gap left by a proper adjoined subalgebra.
-/

namespace GaloisForLFunctions.HTGeometry

/-- An algebraic generator is Runge dense. -/
theorem oneGeneratorRungeDense_of_adjoin_eq_top
    (C A : Type*) [CommSemiring C] [Semiring A] [Algebra C A]
    [TopologicalSpace A] [IsTopologicalSemiring A] {r : A}
    (h : Algebra.adjoin C ({r} : Set A) = ⊤) :
    OneGeneratorRungeDense C A r := by
  refine le_antisymm le_top ?_
  rw [← h]
  exact Subalgebra.le_topologicalClosure _

end GaloisForLFunctions.HTGeometry
