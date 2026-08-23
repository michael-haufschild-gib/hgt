/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CubicCyclicGaloisAlgebraSplittingTowers
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2Split

/-!
# Cubic cyclic `H²` parameters as Brauer classes

For a cyclic Galois extension of degree three, every nonzero cyclic parameter produces a central
simple algebra. This module packages its `H²` class as a Brauer class and proves compatibility
with the cyclic norm quotient, including that the zero parameter is split. It is a function,
not yet an additive homomorphism: tensor-product compatibility is separate infrastructure.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- A selected cubic central simple algebra for a cyclic degree-three cohomology class. -/
noncomputable def cubicCyclicGaloisH2ClassCSA [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : cyclicGaloisH2 K L) : CSA K :=
  cubicCyclicGaloisH2ParameterCSA K L hdeg
    (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
      (cyclicGaloisH2Representative K L z)))

/-- The Brauer class selected by a cubic cyclic degree-two cohomology class. -/
noncomputable def cubicCyclicGaloisH2BrauerMap [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) : cyclicGaloisH2 K L → BrauerGroup K :=
  fun z ↦ brauerClass (cubicCyclicGaloisH2ClassCSA K L hdeg z)

/-- A degree-three cyclic norm quotient presented as `ℤ/3ℤ` supplies a concrete Brauer parameter
map. This is not yet asserted to be an additive homomorphism: tensor-product compatibility of
cubic cyclic algebras remains separate infrastructure. -/
noncomputable def cubicCyclicNormQuotientBrauerMap [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 3) :
    ZMod 3 → BrauerGroup K :=
  fun z ↦ cubicCyclicGaloisH2BrauerMap K L hdeg
    (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z))

/-- Norm-equivalent cubic cyclic parameters have equal Brauer classes. -/
theorem cubicCyclicGaloisH2Parameter_brauerClass_eq_of_baseProjection_eq
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (a b : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = cyclicGaloisH2BaseProjection K L b) :
    brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg a) =
      brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg b) := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_implies_nonempty_algEquiv K L a b h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A cubic parameter maps to the Brauer representative selected by its degree-three class. -/
theorem cubicCyclicGaloisH2Parameter_brauerClass_eq_brauerMap_of_baseProjection
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (a : Additive Kˣ) (z : cyclicGaloisH2 K L)
    (h : cyclicGaloisH2BaseProjection K L a = z) :
    brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg a) =
      cubicCyclicGaloisH2BrauerMap K L hdeg z := by
  obtain ⟨e⟩ := cyclicGaloisH2BaseProjection_eq_class_implies_nonempty_algEquiv K L a z h
  exact brauerClass_eq_of_algEquiv _ _ e

/-- A vanishing cubic cyclic degree-two parameter represents the split Brauer class. -/
theorem cubicCyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (a : Additive Kˣ)
    (h : cyclicGaloisH2BaseProjection K L a = 0) :
    brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg a) = brauerSplitClass K := by
  calc
    brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg a) =
        brauerClass (cyclicGaloisH2ZeroCSA K L a h) := by
      exact brauerClass_eq_of_algEquiv _ _ AlgEquiv.refl
    _ = brauerSplitClass K := brauerClass_cyclicGaloisH2ZeroCSA_eq_split K L a h

/-- The zero cyclic degree-two cohomology class maps to the split Brauer class. -/
theorem cubicCyclicGaloisH2BrauerMap_zero_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) :
    cubicCyclicGaloisH2BrauerMap K L hdeg 0 = brauerSplitClass K := by
  apply cubicCyclicGaloisH2Parameter_brauerClass_eq_split_of_baseProjection_eq_zero K L hdeg
  exact cyclicGaloisH2ClassCyclicAlgebra_baseParameter_projection K L 0

/-- The zero residue class in a cubic norm-quotient parameterization is split. -/
theorem cubicCyclicNormQuotientBrauerMap_zero_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 3) :
    cubicCyclicNormQuotientBrauerMap K L hdeg e 0 = brauerSplitClass K := by
  change cubicCyclicGaloisH2BrauerMap K L hdeg
    (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm 0)) = brauerSplitClass K
  rw [map_zero, map_zero]
  exact cubicCyclicGaloisH2BrauerMap_zero_eq_split K L hdeg

/-- Every cubic cyclic degree-two class is split by its defining cubic Galois extension. -/
theorem scalarExtensionBrauerMap_cubicCyclicGaloisH2BrauerMap_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K L (cubicCyclicGaloisH2BrauerMap K L hdeg z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
      (brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg
        (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z))))) = brauerSplitClass L
  apply scalarExtensionBrauerMap_cubicCyclicGaloisAlgebraCSA_eq_split K L hdeg

/-- Every cubic norm-quotient Brauer parameter is split by its defining cubic extension. Thus the
map lands in the relative Brauer kernel. -/
theorem scalarExtensionBrauerMap_cubicCyclicNormQuotientBrauerMap_eq_split
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3)
    (e : Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L ≃+ ZMod 3) (z : ZMod 3) :
    scalarExtensionBrauerMap K L (cubicCyclicNormQuotientBrauerMap K L hdeg e z) =
      brauerSplitClass L := by
  change scalarExtensionBrauerMap K L
    (cubicCyclicGaloisH2BrauerMap K L hdeg
      (cyclicGaloisH2BaseNormQuotientEquiv K L (e.symm z))) = brauerSplitClass L
  exact scalarExtensionBrauerMap_cubicCyclicGaloisH2BrauerMap_eq_split K L hdeg _

/-- Every scalar extension through the defining cubic Galois field kills the Brauer class of a
cubic cyclic degree-two cohomology class. -/
theorem scalarExtensionBrauerMap_cubicCyclicGaloisH2BrauerMap_eq_split_of_scalarTower
    {E : Type} [Field E] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [IsGalois K L]
    (hdeg : Module.finrank K L = 3) (z : cyclicGaloisH2 K L) :
    scalarExtensionBrauerMap K E (cubicCyclicGaloisH2BrauerMap K L hdeg z) =
      brauerSplitClass E := by
  change scalarExtensionBrauerMap K E
      (brauerClass (cubicCyclicGaloisH2ParameterCSA K L hdeg
        (Additive.ofMul (cyclicGaloisH2FixedBaseUnit K L
          (cyclicGaloisH2Representative K L z))))) = brauerSplitClass E
  apply scalarExtensionBrauerMap_cubicCyclicGaloisAlgebraCSA_eq_split_of_scalarTower
    K L E hdeg

end GaloisForLFunctions.HTGeometry.ABHN
