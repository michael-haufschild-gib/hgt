import GaloisForLFunctions.HTGeometry.BuildingConnected
import GaloisForLFunctions.HTGeometry.FiniteSubmoduleLattice

/-!
# Finite vertex type for a spherical building

The vertices of the spherical building of a finite vector space are its nonzero proper subspaces.
This module supplies their finite enumeration from `submoduleFintype`, so the existing abstract
building can be used as a finite weighted complex.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

noncomputable section

/-- A finite enumeration of the nonzero proper subspaces of a finite module. -/
@[reducible] noncomputable def properPartSubmoduleFintype {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [Fintype M] : Fintype (properPart (Submodule R M)) := by
  letI : Fintype (Submodule R M) := submoduleFintype
  exact Fintype.ofFinite _

end

end GaloisForLFunctions.HTGeometry
