import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite submodule lattices

When a module has finitely many elements, its lattice of submodules is finite: a submodule is
determined by its carrier, and the powerset of a finite type is finite.  This is the enumeration
infrastructure needed to make finite spherical buildings into finite weighted complexes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite enumeration of the submodule lattice of a finite module. -/
@[reducible] noncomputable def submoduleFintype {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype M] : Fintype (Submodule R M) :=
  Fintype.ofInjective (fun S : Submodule R M => (S : Set M)) (fun _ _ h => SetLike.ext' h)

end

end GaloisForLFunctions.HTGeometry
