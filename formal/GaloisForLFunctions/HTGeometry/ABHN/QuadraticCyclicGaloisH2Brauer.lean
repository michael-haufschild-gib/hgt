/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebra
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebraSplit
import GaloisForLFunctions.HTGeometry.ABHN.QuadraticCyclicGaloisAlgebraSplittingFields
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2Split

/-!
# Quadratic cyclic `H²` parameters as Brauer classes

For a cyclic Galois extension of degree two, every nonzero cyclic parameter now produces a
central simple algebra.  Norm-equivalent parameters are already explicitly isomorphic as raw
algebras.  This module combines these facts to give equality of their Brauer classes and a
chosen Brauer representative for every cyclic degree-two cohomology class.

The result is a closed degree-two cohomology-to-Brauer bridge.  It is deliberately a function,
not yet an additive homomorphism: compatibility of tensor products of cyclic algebras with
addition of cohomology parameters is separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- A selected quadratic central simple algebra for a cyclic degree-two cohomology class. -/
noncomputable def quadraticCyclicGaloisH2ClassCSA [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) : CSA K :=
  quadraticCyclicGaloisH2ParameterCSA K L hdeg
    (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
      (cyclicGaloisH2Representative K L z)))

/-- The Brauer class selected by a quadratic cyclic degree-two cohomology class. -/
noncomputable def quadraticCyclicGaloisH2BrauerMap [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) : cyclicGaloisH2 K L → BrauerGroup K :=
  fun z ↦ brauerClass (quadraticCyclicGaloisH2ClassCSA K L hdeg z)

/-- Norm-equivalent quadratic cyclic parameters have equal Brauer classes. -/
theorem quadraticCyclicGaloisH2Parameter_brauerClass_eq_of_baseProjection_eq
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (a b : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b) :
    brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg a) =
      brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg b) := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_implies_nonempty_algEquiv K L a b h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A quadratic parameter maps to the Brauer representative selected by its degree-two class. -/
theorem quadraticCyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (a : Additive Kˣ) (z : cyclicGaloisH2 K L)
    (h : cyclicGaloisH2BaseProjection K L a = z) :
    brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg a) =
      quadraticCyclicGaloisH2BrauerMap K L hdeg z := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_class_implies_nonempty_algEquiv K L a z h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A vanishing quadratic cyclic degree-two parameter represents the split Brauer class. -/
theorem quadraticCyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (a : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = 0) :
    brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg a) = brauerSplitClass K := by
  calc
    brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg a) =
        brauerClass (cyclicGaloisH2ZeroCSA K L a h) := by
      exact brauerClass_eq_of_algEquiv _ _ AlgEquiv.refl
    _ = brauerSplitClass K := brauerClass_cyclicGaloisH2ZeroCSA_eq_split K L a h

/-- The zero cyclic degree-two cohomology class maps to the split Brauer class. -/
theorem quadraticCyclicGaloisH2BrauerMap_zero_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) :
    quadraticCyclicGaloisH2BrauerMap K L hdeg 0 = brauerSplitClass K := by
  apply quadraticCyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero K L hdeg
  exact cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection K L 0

/-- Every quadratic cyclic degree-two class is split by its defining quadratic Galois
extension. -/
theorem scalarExtensionBrauerMap_quadraticCyclicGaloisH2BrauerMap_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K L (quadraticCyclicGaloisH2BrauerMap K L hdeg z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
      (brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg
        (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z))))) = brauerSplitClass L
  apply scalarExtensionBrauerMap_quadraticCyclicGaloisAlgebraCSA_eq_split K L hdeg

/-- Every scalar extension through the defining quadratic Galois field kills the Brauer class of
a quadratic cyclic degree-two cohomology class. -/
theorem scalarExtensionBrauerMap_quadraticCyclicGaloisH2BrauerMap_eq_split_of_scalarTower
    {E : Type} [Field E] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 2) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K E (quadraticCyclicGaloisH2BrauerMap K L hdeg z) =
      brauerSplitClass E := by
  change scalarExtensionBrauerMap K E
      (brauerClass (quadraticCyclicGaloisH2ParameterCSA K L hdeg
        (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z))))) = brauerSplitClass E
  apply scalarExtensionBrauerMap_quadraticCyclicGaloisAlgebraCSA_eq_split_of_scalarTower
    K L E hdeg

end GaloisForLFunctions.HTGeometry.ABHN
