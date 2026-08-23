/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseLocalGlobal
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariantValues

/-!
# Hasse detection of regular invariants in cyclic Galois algebras

The all-degree cyclic Galois central simple algebra inherits completionwise detection of its
regular characteristic polynomial, trace, and norm.  These are fixed-element identities, not
the global reciprocity relation for local Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- The regular characteristic polynomial of a cyclic Galois algebra element over a number
field is determined by its values at every completion. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (p : Polynomial K) :
    (LinearMap.mulLeft K x).charpoly = p ↔ ∀ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly =
          p.map (algebraMap K (completion K v)) :=
  numberField_regularCharpoly_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x p

/-- The regular trace of a cyclic Galois algebra element over a number field is determined by
its values at every completion. -/
theorem numberField_cyclicGaloisAlgebra_regularTrace_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a) (LinearMap.mulLeft K x) = c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)) =
          algebraMap K (completion K p) c :=
  numberField_regularTrace_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- The regular norm of a cyclic Galois algebra element over a number field is determined by
its values at every completion. -/
theorem numberField_cyclicGaloisAlgebra_regularNorm_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.det (LinearMap.mulLeft K x) = c ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)) =
          algebraMap K (completion K p) c :=
  numberField_regularNorm_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- The regular characteristic polynomial of a cyclic Galois algebra element over `F(t)` is
determined by its values at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (p : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x).charpoly = p ↔ ∀ v : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F v)
        (rationalFunctionLocalScalarExtensionMap F v
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) :=
  rationalFunction_regularCharpoly_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x p

/-- The regular trace of a cyclic Galois algebra element over `F(t)` is determined by its values
at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularTrace_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x) = c ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a)
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunction_regularTrace_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

/-- The regular norm of a cyclic Galois algebra element over `F(t)` is determined by its values
at every finite and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularNorm_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) x) = c ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunction_regularNorm_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

/-- A prescribed regular characteristic polynomial of a nonzero cyclic Galois algebra over a
number field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (p : Polynomial K) :
    (LinearMap.mulLeft K x).charpoly = p ↔ ∃ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v (cyclicGaloisAlgebraCSA K L a ha) x)).charpoly =
          p.map (algebraMap K (completion K v)) :=
  numberField_regularCharpoly_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x p

/-- A prescribed regular trace of a nonzero cyclic Galois algebra element over a number field
can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a) (LinearMap.mulLeft K x) = c ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.trace (completion K p)
          (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)) =
          algebraMap K (completion K p) c :=
  numberField_regularTrace_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- A prescribed regular norm of a nonzero cyclic Galois algebra element over a number field
can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a c : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    LinearMap.det (LinearMap.mulLeft K x) = c ↔ ∃ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x)) =
          algebraMap K (completion K p) c :=
  numberField_regularNorm_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x c

/-- A prescribed regular characteristic polynomial of a nonzero cyclic Galois algebra over
`F(t)` can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a)
    (p : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x).charpoly = p ↔ ∃ v : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F v)
        (rationalFunctionLocalScalarExtensionMap F v
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) :=
  rationalFunction_regularCharpoly_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x p

/-- A prescribed regular trace of a nonzero cyclic Galois algebra element over `F(t)` can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x) = c ↔ ∃ p : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a)
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunction_regularTrace_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

/-- A prescribed regular norm of a nonzero cyclic Galois algebra element over `F(t)` can be
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a c : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) x) = c ↔ ∃ p : RationalFunctionPlace F,
      LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p
          (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunction_regularNorm_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x c

end GaloisForLFunctions.HTGeometry.ABHN
