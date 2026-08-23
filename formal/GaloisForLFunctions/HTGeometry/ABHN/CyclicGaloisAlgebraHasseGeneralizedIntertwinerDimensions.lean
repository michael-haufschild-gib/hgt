/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedIntertwinerDimensions

/-!
# Hasse-local generalized Sylvester kernels for cyclic Galois algebras

For two fixed cyclic-algebra elements and a fixed scalar, every generalized eigenspace of the
Sylvester map `z ↦ x * z - z * y` has the same dimension at every completion. Prescribed
dimensions are therefore detected globally at all completions or at a single completion. This
retains the full finite generalized-intertwiner profile without asserting local Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A generalized Sylvester kernel in a nonzero cyclic Galois algebra over a number field has the
same dimension at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_completion
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K)
    (n : ℕ) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker
      ((LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
        LinearMap.mulRight (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y) -
        (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker
        ((LinearMap.mulLeft K x - LinearMap.mulRight K y - c • LinearMap.id) ^ n)) :=
  numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion K
    (cyclicGaloisAlgebraCSA K L a ha) x y c n p

/-- A generalized Sylvester kernel in a nonzero cyclic Galois algebra over a global function
field has the same dimension at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_completion
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F)
    (n : ℕ) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
      ((LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
        LinearMap.mulRight (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) =
      Module.finrank (RatFunc F) (LinearMap.ker
        ((LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y -
          c • LinearMap.id) ^ n)) :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c n p

/-- A prescribed generalized Sylvester-kernel dimension in a nonzero cyclic Galois algebra over a
number field is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K x - LinearMap.mulRight K y - c • LinearMap.id) ^ n)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
    K (cyclicGaloisAlgebraCSA K L a ha) x y c n d

/-- A prescribed generalized Sylvester-kernel dimension in a nonzero cyclic Galois algebra over a
global function field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y -
        c • LinearMap.id) ^ n)) = d ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
    F (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c n d

/-- A prescribed generalized Sylvester-kernel dimension in a nonzero cyclic Galois algebra over a
number field is certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K x - LinearMap.mulRight K y - c • LinearMap.id) ^ n)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d :=
  numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
    K (cyclicGaloisAlgebraCSA K L a ha) x y c n d

/-- A prescribed generalized Sylvester-kernel dimension in a nonzero cyclic Galois algebra over a
global function field is certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y -
        c • LinearMap.id) ^ n)) = d ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d :=
  rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
    F (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c n d

end GaloisForLFunctions.HTGeometry.ABHN
