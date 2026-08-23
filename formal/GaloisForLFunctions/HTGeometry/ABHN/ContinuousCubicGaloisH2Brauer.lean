/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisH2Brauer

/-!
# Continuous cubic Galois `H²` classes in the Brauer group

For a finite cubic cyclic Galois extension, continuous degree-two unit cohomology agrees with
ordinary Galois cohomology. Composing this comparison with the cubic cyclic construction gives a
closed continuous-cohomology-to-Brauer map. It is a finite-level component of the local
class-field-theory bridge, not yet a local invariant isomorphism.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

/-- The cubic cyclic Brauer representative of a continuous degree-two unit cohomology class for
a finite Galois extension. -/
noncomputable def finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) :
    continuousGaloisUnitCohomology 2 K L → BrauerGroup K :=
  fun z ↦ cubicCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- The zero continuous degree-two class has split cubic cyclic Brauer representative. -/
theorem finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) :
    finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg 0 =
      brauerSplitClass K := by
  change cubicCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L 0) = brauerSplitClass K
  rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).map_zero]
  exact cubicCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

/-- The defining finite cubic Galois field splits every continuous cyclic cohomology Brauer
representative. -/
theorem scalarExtensionBrauerMap_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : continuousGaloisUnitCohomology 2 K L) :
    scalarExtensionBrauerMap K L
      (finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg z) =
        brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (cubicCyclicGaloisH2BrauerMap K L hdeg
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) = brauerSplitClass L
  exact scalarExtensionBrauerMap_cubicCyclicGaloisH2BrauerMap_eq_split K L hdeg _

/-- Every scalar extension through the defining cubic Galois field kills the Brauer class
selected by a continuous cyclic degree-two class. -/
theorem scalarExtensionBrauerMap_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split_of_scalarTower
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    {E : Type} [Field E] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : continuousGaloisUnitCohomology 2 K L) :
    scalarExtensionBrauerMap K E
      (finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg z) =
        brauerSplitClass E := by
  change scalarExtensionBrauerMap K E
    (cubicCyclicGaloisH2BrauerMap K L hdeg
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) = brauerSplitClass E
  exact scalarExtensionBrauerMap_cubicCyclicGaloisH2BrauerMap_eq_split_of_scalarTower
    K L hdeg _

/-- Over a finite base field, every continuous cubic cyclic degree-two class selects the split
Brauer class. -/
theorem finiteField_finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)] [Finite L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap K L hdeg z =
      brauerSplitClass K := by
  rw [show z = 0 by exact finiteField_continuousGaloisH2_eq_zero z]
  exact finiteGaloisContinuousCubicCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

end GaloisForLFunctions.HTGeometry.ABHN
