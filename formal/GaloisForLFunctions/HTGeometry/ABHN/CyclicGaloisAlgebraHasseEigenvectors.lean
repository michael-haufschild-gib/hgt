/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEigenvectors

/-!
# Hasse-local regular eigenvalues for cyclic Galois algebras

For a fixed scalar and element of a nonzero cyclic Galois algebra, the existence of a nonzero
left regular eigenvector is detected at all completions and at any one completion.  This is a
spectral statement about one globally fixed scalar; it does not assemble independently chosen
local eigenvectors or compute local Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A fixed scalar is a left-regular eigenvalue in a nonzero cyclic Galois algebra over a number
field exactly when it is one at every completion. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) ≠ ⊥ ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          (algebraMap K (completion K p) c) • LinearMap.id) ≠ ⊥ :=
  numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- A fixed scalar is a left-regular eigenvalue in a nonzero cyclic Galois algebra over a global
function field exactly when it is one at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ≠ ⊥ ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ≠ ⊥ :=
  rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

/-- A fixed scalar is a left-regular eigenvalue in a nonzero cyclic Galois algebra over a number
field exactly when it is one at some completion. -/
theorem numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) ≠ ⊥ ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          (algebraMap K (completion K p) c) • LinearMap.id) ≠ ⊥ :=
  numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- A fixed scalar is a left-regular eigenvalue in a nonzero cyclic Galois algebra over a global
function field exactly when it is one at some completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ≠ ⊥ ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ≠ ⊥ :=
  rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

end GaloisForLFunctions.HTGeometry.ABHN
