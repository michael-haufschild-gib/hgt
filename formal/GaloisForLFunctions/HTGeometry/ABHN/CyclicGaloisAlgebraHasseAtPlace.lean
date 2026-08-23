/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseLocalGlobal

/-!
# One-place Hasse descent for cyclic Galois-algebra elements

For every fixed element or one-sided division equation in a nonzero cyclic Galois algebra, every
completion is faithfully flat.  Consequently its unit, zero-divisor, and division behavior at
any selected completion is equivalent to its global behavior.  This is stronger than an all-place
test, but does not patch independently chosen local elements.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A fixed element of a nonzero cyclic Galois algebra over a number field is a unit exactly
when its image is a unit at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_isUnit_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    IsUnit x ↔ IsUnit (numberFieldLocalScalarExtensionMap K p
      (cyclicGaloisAlgebraCSA K L a ha) x) := by
  exact scalarExtensionMap_isUnit_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` is a unit exactly when its
image is a unit at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isUnit_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsUnit x ↔ IsUnit (rationalFunctionLocalScalarExtensionMap F p
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) := by
  exact scalarExtensionMap_isUnit_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed number-field cyclic Galois-algebra element has a nonzero left annihilator exactly
when its image has one at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed number-field cyclic Galois-algebra element has a nonzero right annihilator exactly
when its image has one at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed global-function-field cyclic Galois-algebra element has a nonzero left annihilator
exactly when its image has one at any specified completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed global-function-field cyclic Galois-algebra element has a nonzero right annihilator
exactly when its image has one at any specified completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed left-division equation in a nonzero cyclic Galois algebra over a number field is
solvable globally exactly when it is solvable at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, x * z = y) ↔ ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y := by
  exact scalarExtensionMap_exists_mulLeft_eq_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A fixed right-division equation in a nonzero cyclic Galois algebra over a number field is
solvable globally exactly when it is solvable at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulRight_eq_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, z * x = y) ↔ ∃ z,
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y := by
  exact scalarExtensionMap_exists_mulRight_eq_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A fixed left-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable
globally exactly when it is solvable at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, x * z = y) ↔ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y := by
  exact scalarExtensionMap_exists_mulLeft_eq_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A fixed right-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable
globally exactly when it is solvable at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulRight_eq_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, z * x = y) ↔ ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y := by
  exact scalarExtensionMap_exists_mulRight_eq_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

end GaloisForLFunctions.HTGeometry.ABHN
