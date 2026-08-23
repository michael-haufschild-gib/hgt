/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisAlgebraSplit
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionFunctoriality

/-!
# Scalar towers through cubic cyclic splitting fields

The cubic splitting theorem is stable under every further scalar extension through the defining
cyclic Galois field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

variable (K L E : Type) [Field K] [Field L] [Field E]
  [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

/-- Every scalar extension through the defining cubic Galois field splits a nonzero cubic cyclic
Brauer class. -/
theorem scalarExtensionBrauerMap_cubicCyclicGaloisAlgebraCSA_eq_split_of_scalarTower
    (hdeg : Module.finrank K L = 3) (a : K) (ha : a ≠ 0) :
    scalarExtensionBrauerMap K E
      (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) = brauerSplitClass E := by
  calc
    scalarExtensionBrauerMap K E
        (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha)) =
        scalarExtensionBrauerMap L E (scalarExtensionBrauerMap K L
          (brauerClass (cubicCyclicGaloisAlgebraCSA K L hdeg a ha))) :=
      (scalarExtensionBrauerMap_comp K L E _).symm
    _ = scalarExtensionBrauerMap L E (brauerSplitClass L) := by
      rw [scalarExtensionBrauerMap_cubicCyclicGaloisAlgebraCSA_eq_split K L hdeg a ha]
    _ = brauerSplitClass E := scalarExtensionBrauerMap_split L E

end GaloisForLFunctions.HTGeometry.ABHN
