/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerDimensions

/-!
# Hasse tests for intertwiners in cyclic Galois algebras

For a nonzero cyclic Galois algebra, the Sylvester equation `a*x - x*b = c` and the dimension
of its homogeneous solution space are detected after scalar extension to completions.  A
nonzero homogeneous solution is an intertwiner between the two left-multiplication actions;
its dimension records a conjugacy-relevant multiplicity invariant.

These are fixed-global-element tests.  They neither patch unrelated local conjugacies nor
identify local Brauer classes with local invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- An inhomogeneous intertwining equation in a nonzero cyclic Galois algebra over a number
field is solvable exactly when it is solvable at every completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra K L a) :
    (∃ w, x * w - w * y = z) ↔ ∀ p : NumberFieldPlace K, ∃ w,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * w -
        w * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y =
          numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) z :=
  numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y z

/-- An inhomogeneous intertwining equation in a nonzero cyclic Galois algebra over a global
function field is solvable exactly when it is solvable at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ w, x * w - w * y = z) ↔ ∀ p : RationalFunctionPlace F, ∃ w,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * w -
        w * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) z :=
  rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y z

/-- An inhomogeneous intertwining equation in a nonzero cyclic Galois algebra over a number
field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra K L a) :
    (∃ w, x * w - w * y = z) ↔ ∃ p : NumberFieldPlace K, ∃ w,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * w -
        w * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y =
          numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) z :=
  numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y z

/-- An inhomogeneous intertwining equation in a nonzero cyclic Galois algebra over a global
function field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y z : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ w, x * w - w * y = z) ↔ ∃ p : RationalFunctionPlace F, ∃ w,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * w -
        w * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) z :=
  rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y z

/-- Existence of a nonzero intertwiner in a nonzero cyclic Galois algebra over a number field is
detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- Existence of a nonzero intertwiner in a nonzero cyclic Galois algebra over a global function
field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
          z * rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- Existence of a nonzero intertwiner in a nonzero cyclic Galois algebra over a number field
can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∃ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- Existence of a nonzero intertwiner in a nonzero cyclic Galois algebra over a global function
field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, z ≠ 0 ∧ x * z = z * y) ↔ ∃ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
          z * rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A prescribed intertwiner-space dimension in a nonzero cyclic Galois algebra over a number
field is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K y)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y))) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y d

/-- A prescribed intertwiner-space dimension in a nonzero cyclic Galois algebra over a global
function field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y d

/-- A prescribed intertwiner-space dimension in a nonzero cyclic Galois algebra over a number
field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K y)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y))) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y d

/-- A prescribed intertwiner-space dimension in a nonzero cyclic Galois algebra over a global
function field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y d

end GaloisForLFunctions.HTGeometry.ABHN
