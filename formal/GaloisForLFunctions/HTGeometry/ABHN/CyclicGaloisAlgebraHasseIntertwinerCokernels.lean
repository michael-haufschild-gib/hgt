/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerCokernels

/-!
# Hasse tests for Sylvester cokernel dimensions in cyclic Galois algebras

For a nonzero cyclic Galois algebra, the cokernel of `w ↦ x * w - w * y` is the obstruction
space for the equation `x * w - w * y = z`.  Its dimension is invariant under scalar extension,
so every completed local algebra has exactly the same obstruction count.  This supplements the
existing kernel/intertwiner dimension: the two are related by rank-nullity but have distinct
deformation-theoretic roles.

All statements concern one fixed global pair `x, y`; they do not assemble unrelated local data.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- The Sylvester-cokernel dimension of a nonzero cyclic Galois algebra is unchanged at each
number-field completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_completion
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (p : NumberFieldPlace K) :
    Module.finrank (completion K p)
      ((completion K p ⊗[K] cyclicGaloisAlgebra K L a) ⧸ LinearMap.range
        (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y))) =
      Module.finrank K
        (cyclicGaloisAlgebra K L a ⧸ LinearMap.range
          (LinearMap.mulLeft K x - LinearMap.mulRight K y)) :=
  numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion K
    (cyclicGaloisAlgebraCSA K L a ha) x y p

/-- The Sylvester-cokernel dimension of a nonzero cyclic Galois algebra is unchanged at each
global-function-field completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_completion
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      ((rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) ⧸
        LinearMap.range
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) =
      Module.finrank (RatFunc F)
        (cyclicGaloisAlgebra (RatFunc F) L a ⧸ LinearMap.range
          (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_completion F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y p

/-- A prescribed Sylvester-cokernel dimension in a nonzero cyclic Galois algebra over a number
field is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K
      (cyclicGaloisAlgebra K L a ⧸ LinearMap.range
        (LinearMap.mulLeft K x - LinearMap.mulRight K y)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          ((completion K p ⊗[K] cyclicGaloisAlgebra K L a) ⧸ LinearMap.range
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y))) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y d

/-- A prescribed Sylvester-cokernel dimension in a nonzero cyclic Galois algebra over a global
function field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (cyclicGaloisAlgebra (RatFunc F) L a ⧸ LinearMap.range
        (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) ⧸
            LinearMap.range
              (LinearMap.mulLeft (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
                LinearMap.mulRight (rationalFunctionCompletion F p)
                  (rationalFunctionLocalScalarExtensionMap F p
                    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y d

/-- A prescribed Sylvester-cokernel dimension in a nonzero cyclic Galois algebra over a number
field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K
      (cyclicGaloisAlgebra K L a ⧸ LinearMap.range
        (LinearMap.mulLeft K x - LinearMap.mulRight K y)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          ((completion K p ⊗[K] cyclicGaloisAlgebra K L a) ⧸ LinearMap.range
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y))) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y d

/-- A prescribed Sylvester-cokernel dimension in a nonzero cyclic Galois algebra over a global
function field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (cyclicGaloisAlgebra (RatFunc F) L a ⧸ LinearMap.range
        (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) ⧸
            LinearMap.range
              (LinearMap.mulLeft (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
                LinearMap.mulRight (rationalFunctionCompletion F p)
                  (rationalFunctionLocalScalarExtensionMap F p
                    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y))) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y d

end GaloisForLFunctions.HTGeometry.ABHN
