/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisH2Brauer
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology

/-!
# Finite-field cubic cyclic cohomology classes in the Brauer group

For a finite cyclic Galois extension of degree three, degree-two cohomology of units vanishes.
Consequently, every cubic cyclic degree-two class has split selected Brauer representative. This
is the cubic finite-residue component of the cyclic cohomology-to-Brauer bridge.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

/-- Every cubic cyclic degree-two class over a finite field selects the split Brauer class. -/
theorem finiteField_cubicCyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)] [Finite L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : cyclicGaloisH2 K L) :
    cubicCyclicGaloisH2BrauerMap K L hdeg z = brauerSplitClass K := by
  rw [show z = 0 by exact finiteField_H2_eq_zero z]
  exact cubicCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

end GaloisForLFunctions.HTGeometry.ABHN
