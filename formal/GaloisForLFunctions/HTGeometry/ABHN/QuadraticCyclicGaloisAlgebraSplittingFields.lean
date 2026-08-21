/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebraSplit
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionFunctoriality

/-!
# Splitting fields of quadratic cyclic Galois algebras

The defining quadratic Galois field splits its nonzero cyclic algebra.  By functoriality, every
field extension lying over that defining field splits it as well.  This is the form used at a
local place once its completed field carries an `L`-algebra structure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L E : Type) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Every scalar extension through the defining quadratic Galois field splits a nonzero
quadratic cyclic Brauer class. -/
theorem scalarExtensionBrauerMap_quadraticCyclicGaloisAlgebraCSA_eq_split_of_scalarTower
    (hdeg : Module.finrank K L = 2) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K E
      (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) = brauerSplitClass E := by
  calc
    scalarExtensionBrauerMap K E
        (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha)) =
        scalarExtensionBrauerMap L E (scalarExtensionBrauerMap K L
          (brauerClass (quadraticCyclicGaloisAlgebraCSA K L hdeg a ha))) :=
      (scalarExtensionBrauerMap_comp K L E _).symm
    _ = scalarExtensionBrauerMap L E (brauerSplitClass L) := by
      rw [scalarExtensionBrauerMap_quadraticCyclicGaloisAlgebraCSA_eq_split K L hdeg a ha]
    _ = brauerSplitClass E := scalarExtensionBrauerMap_split L E

end GaloisForLFunctions.HTGeometry.ABHN
