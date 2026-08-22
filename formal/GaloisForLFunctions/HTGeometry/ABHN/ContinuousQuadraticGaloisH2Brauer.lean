/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisH2Brauer

/-!
# Continuous quadratic Galois `H²` classes in the Brauer group

For a finite quadratic cyclic Galois extension, the continuous cohomology object agrees with
ordinary Galois cohomology.  Composing that comparison with the existing quadratic cyclic
construction gives a closed continuous-cohomology-to-Brauer map.  This supplies the finite-level
cohomological interface used by local class field theory, but is not a local invariant map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

/-- The quadratic cyclic Brauer representative of a continuous degree-two unit cohomology
class for a finite Galois extension. -/
noncomputable def finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) :
    continuousGaloisUnitCohomology 2 K L → BrauerGroup K :=
  fun z ↦ quadraticCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)

/-- The zero continuous degree-two class has split quadratic cyclic Brauer representative. -/
theorem finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_zero_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg 0 =
      brauerSplitClass K := by
  change quadraticCyclicGaloisH2BrauerMap K L hdeg
    (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L 0) = brauerSplitClass K
  rw [(finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L).map_zero]
  exact quadraticCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

/-- The defining finite quadratic Galois field splits every continuous cyclic cohomology
Brauer representative. -/
theorem scalarExtensionBrauerMap_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : continuousGaloisUnitCohomology 2 K L) :
    scalarExtensionBrauerMap K L
      (finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z) =
        brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (quadraticCyclicGaloisH2BrauerMap K L hdeg
      (finiteGaloisContinuousH2ToOrdinaryH2AddEquiv K L z)) = brauerSplitClass L
  exact scalarExtensionBrauerMap_quadraticCyclicGaloisH2BrauerMap_eq_split K L hdeg _

/-- Over a finite base field, every continuous quadratic cyclic degree-two class selects the
split Brauer class.  This is the continuous version of the finite residue-field computation. -/
theorem finiteField_finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_eq_split
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)] [Finite L]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : continuousGaloisUnitCohomology 2 K L) :
    finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap K L hdeg z =
      brauerSplitClass K := by
  rw [show z = 0 by exact finiteField_continuousGaloisH2_eq_zero z]
  exact finiteGaloisContinuousQuadraticCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

end GaloisForLFunctions.HTGeometry.ABHN
