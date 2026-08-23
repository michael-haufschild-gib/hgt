/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraZeroDivisors
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision

/-!
# Hasse tests for arbitrary-degree cyclic Galois algebras

Every nonzero finite cyclic Galois algebra is a central simple algebra by the all-degree
companion construction.  The fixed-element Hasse principles already proved for central simple
algebras therefore specialize to its units, one-sided zero divisors, and one-sided division
equations over number fields and global function fields.

These results detect a property of one fixed global element or equation.  They do not patch
independently selected local elements and do not assert Albert--Brauer--Hasse--Noether.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A fixed element of a nonzero cyclic Galois algebra over a number field is a unit exactly
when its image is a unit at every completion. -/
theorem numberField_cyclicGaloisAlgebra_isUnit_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    IsUnit x ↔ ∀ p : NumberFieldPlace K,
      IsUnit (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) :=
  numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` is a unit exactly when its
image is a unit at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isUnit_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsUnit x ↔ ∀ p : RationalFunctionPlace F,
      IsUnit (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over a number field has a nonzero left
annihilator exactly when every completion has one. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z = 0 :=
  numberField_exists_nonzero_mulLeft_eq_zero_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over a number field has a nonzero right
annihilator exactly when every completion has one. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x = 0 :=
  numberField_exists_nonzero_mulRight_eq_zero_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` has a nonzero left
annihilator exactly when every finite and infinite completion has one. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z = 0 :=
  rationalFunction_exists_nonzero_mulLeft_eq_zero_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` has a nonzero right
annihilator exactly when every finite and infinite completion has one. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x = 0 :=
  rationalFunction_exists_nonzero_mulRight_eq_zero_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A left-division equation in a nonzero cyclic Galois algebra over a number field is solvable
exactly when it is solvable at every completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, x * z = y) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A right-division equation in a nonzero cyclic Galois algebra over a number field is solvable
exactly when it is solvable at every completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulRight_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, z * x = y) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A left-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable exactly
when it is solvable at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, x * z = y) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A right-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable exactly
when it is solvable at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulRight_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, z * x = y) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

end GaloisForLFunctions.HTGeometry.ABHN
