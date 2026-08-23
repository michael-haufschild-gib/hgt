/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularCharpolySeparable

/-!
# Hasse spectral tests for cyclic Galois algebras

For a fixed element of a nonzero cyclic Galois algebra, separability of its regular
characteristic polynomial is detected at all completions and at any one completion.  This is the
spectral regularity condition that excludes repeated geometric roots in the left regular action.

It is not a statement about globalizing locally chosen eigenvectors or about local Brauer
invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A nonzero cyclic Galois algebra element over a number field has separable regular
characteristic polynomial exactly when its image does at every completion. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_separable_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    (LinearMap.mulLeft K x).charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly.Separable :=
  numberField_regularCharpoly_separable_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- A nonzero cyclic Galois algebra element over a global function field has separable regular
characteristic polynomial exactly when its image does at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_separable_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (LinearMap.mulLeft (RatFunc F) x).charpoly.Separable ↔ ∀ p : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly.Separable :=
  rationalFunction_regularCharpoly_separable_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- Separability of a nonzero cyclic Galois algebra regular characteristic polynomial over a
number field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    (LinearMap.mulLeft K x).charpoly.Separable ↔ ∃ p : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly.Separable :=
  numberField_regularCharpoly_separable_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Separability of a nonzero cyclic Galois algebra regular characteristic polynomial over a
global function field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (LinearMap.mulLeft (RatFunc F) x).charpoly.Separable ↔ ∃ p : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly.Separable :=
  rationalFunction_regularCharpoly_separable_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

end GaloisForLFunctions.HTGeometry.ABHN
