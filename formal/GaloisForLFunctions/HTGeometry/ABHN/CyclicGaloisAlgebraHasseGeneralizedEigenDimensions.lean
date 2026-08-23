/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedEigenDimensions

/-!
# Hasse-local generalized regular eigenspaces for cyclic Galois algebras

The generalized left-regular eigenspace of a fixed cyclic-algebra element and fixed scalar has
the same dimension at every completion.  Prescribed dimensions are therefore detected globally
at all completions or at a single completion.  This retains the complete finite Jordan-kernel
profile of the regular action without asserting a local Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A generalized left-regular eigenspace of a nonzero cyclic Galois algebra over a number field
has the same dimension at every completion. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_completion
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K)
    (n : ℕ) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker
      ((LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
        (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) :=
  numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion K
    (cyclicGaloisAlgebraCSA K L a ha) x c n p

/-- A generalized left-regular eigenspace of a nonzero cyclic Galois algebra over a global
function field has the same dimension at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_completion
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F)
    (n : ℕ) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
      ((LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) =
      Module.finrank (RatFunc F) (LinearMap.ker
        ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) :=
  rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c n p

/-- A prescribed generalized left-regular eigenspace dimension in a nonzero cyclic Galois algebra
over a number field is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d :=
  numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c n d

/-- A prescribed generalized left-regular eigenspace dimension in a nonzero cyclic Galois algebra
over a global function field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d :=
  rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c n d

/-- A prescribed generalized left-regular eigenspace dimension in a nonzero cyclic Galois algebra
over a number field is certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d :=
  numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c n d

/-- A prescribed generalized left-regular eigenspace dimension in a nonzero cyclic Galois algebra
over a global function field is certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
          ((LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d :=
  rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c n d

end GaloisForLFunctions.HTGeometry.ABHN
