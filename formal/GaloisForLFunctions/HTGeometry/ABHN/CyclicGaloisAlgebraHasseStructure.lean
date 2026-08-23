/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseLocalGlobal
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCenter
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCentralizerDimensions

/-!
# Hasse structure tests for cyclic Galois algebras

The arbitrary-degree cyclic Galois construction is central simple when its parameter is
nonzero.  Consequently, a global cyclic algebra element may be tested at all completions for
centrality, membership in a commutator image, and dimension of its centralizer.  The latter is
the linear-algebraic regularity invariant used to stratify a central simple algebra by
conjugacy type.

All statements concern images of fixed global elements.  They do not identify local Brauer
groups or establish the reciprocity part of Albert--Brauer--Hasse--Noether.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Centrality of a nonzero cyclic Galois algebra element over a number field is detected at
every completion. -/
theorem numberField_cyclicGaloisAlgebra_mem_center_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    x ∈ Subalgebra.center K (cyclicGaloisAlgebra K L a) ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x ∈
        Subalgebra.center (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  numberFieldLocalScalarExtensionMap_mem_center_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Centrality of a nonzero cyclic Galois algebra element over a global function field is
detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mem_center_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    x ∈ Subalgebra.center (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∀ p : RationalFunctionPlace F,
        rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x ∈
          Subalgebra.center (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a) :=
  rationalFunctionLocalScalarExtensionMap_mem_center_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- Centrality of a nonzero cyclic Galois algebra element over a number field can be certified
at one completion. -/
theorem numberField_cyclicGaloisAlgebra_mem_center_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    x ∈ Subalgebra.center K (cyclicGaloisAlgebra K L a) ↔ ∃ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x ∈
        Subalgebra.center (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  numberFieldLocalScalarExtensionMap_mem_center_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Centrality of a nonzero cyclic Galois algebra element over a global function field can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mem_center_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    x ∈ Subalgebra.center (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∃ p : RationalFunctionPlace F,
        rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x ∈
          Subalgebra.center (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a) :=
  rationalFunctionLocalScalarExtensionMap_mem_center_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A commutator equation in a nonzero cyclic Galois algebra over a number field is solvable
exactly when it is solvable at every completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_commutator_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, x * z - z * x = y) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z -
          z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
            numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A commutator equation in a nonzero cyclic Galois algebra over a global function field is
solvable exactly when it is solvable at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_commutator_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, x * z - z * x = y) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z -
        z * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A commutator equation in a nonzero cyclic Galois algebra over a number field can be
certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, x * z - z * x = y) ↔ ∃ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z -
          z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
            numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y :=
  numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A commutator equation in a nonzero cyclic Galois algebra over a global function field can
be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, x * z - z * x = y) ↔ ∃ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z -
        z * rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
          rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y :=
  rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A prescribed centralizer dimension in a nonzero cyclic Galois algebra over a number field
is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K x)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x))) = d :=
  numberFieldLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x d

/-- A prescribed centralizer dimension in a nonzero cyclic Galois algebra over a global function
field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) x)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x))) = d :=
  rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x d

/-- A prescribed centralizer dimension in a nonzero cyclic Galois algebra over a number field
can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K x - LinearMap.mulRight K x)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker
            (LinearMap.mulLeft (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
              LinearMap.mulRight (completion K p)
                (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x))) = d :=
  numberFieldLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x d

/-- A prescribed centralizer dimension in a nonzero cyclic Galois algebra over a global function
field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) x)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p
                  (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x))) = d :=
  rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x d

end GaloisForLFunctions.HTGeometry.ABHN
