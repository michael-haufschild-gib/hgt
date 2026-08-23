/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerInvariants

/-!
# Hasse-local Sylvester spectral invariants for cyclic Galois algebras

For two fixed elements of a nonzero cyclic Galois algebra, the characteristic polynomial, trace,
and determinant of their Sylvester map are preserved at all completions. Specified values can be
checked at every completion or at one completion. These are local-global adjoint-action data,
not local Brauer invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- The Sylvester characteristic polynomial in a nonzero cyclic Galois algebra over a number
field is detected at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (q : Polynomial K) :
    (LinearMap.mulLeft K x - LinearMap.mulRight K y).charpoly = q ↔
      ∀ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)).charpoly =
              q.map (algebraMap K (completion K p)) :=
  numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y q

/-- The Sylvester trace in a nonzero cyclic Galois algebra over a number field is detected at
every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a)
      (LinearMap.mulLeft K x - LinearMap.mulRight K y) = c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)) =
                algebraMap K (completion K p) c :=
  numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y c

/-- The Sylvester determinant in a nonzero cyclic Galois algebra over a number field is detected
at every completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerDet_eq_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.det (LinearMap.mulLeft K x - LinearMap.mulRight K y) = c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)) =
              algebraMap K (completion K p) c :=
  numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y c

/-- The Sylvester characteristic polynomial in a nonzero cyclic Galois algebra over a global
function field is detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y).charpoly = q ↔
      ∀ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)).charpoly =
                q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y q

/-- The Sylvester trace in a nonzero cyclic Galois algebra over a global function field is detected
at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) = c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) =
                  algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c

/-- The Sylvester determinant in a nonzero cyclic Galois algebra over a global function field is
detected at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerDet_eq_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) = c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c

/-- A Sylvester characteristic polynomial in a nonzero cyclic Galois algebra over a number field
is certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (q : Polynomial K) :
    (LinearMap.mulLeft K x - LinearMap.mulRight K y).charpoly = q ↔
      ∃ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)).charpoly =
              q.map (algebraMap K (completion K p)) :=
  numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y q

/-- A Sylvester trace in a nonzero cyclic Galois algebra over a number field is certified at one
completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.trace K (cyclicGaloisAlgebra K L a)
      (LinearMap.mulLeft K x - LinearMap.mulRight K y) = c ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a)
          (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
            LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)) =
                algebraMap K (completion K p) c :=
  numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y c

/-- A Sylvester determinant in a nonzero cyclic Galois algebra over a number field is certified at
one completion. -/
theorem numberField_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) (c : K) :
    LinearMap.det (LinearMap.mulLeft K x - LinearMap.mulRight K y) = c ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x) -
          LinearMap.mulRight (completion K p)
            (numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y)) =
              algebraMap K (completion K p) c :=
  numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x y c

/-- A Sylvester characteristic polynomial in a nonzero cyclic Galois algebra over a global
function field is certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y).charpoly = q ↔
      ∃ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)).charpoly =
                q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) :=
  rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y q

/-- A Sylvester trace in a nonzero cyclic Galois algebra over a global function field is certified
at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)
      (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) = c ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p
                (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) =
                  algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c

/-- A Sylvester determinant in a nonzero cyclic Galois algebra over a global function field is
certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a)
    (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) x - LinearMap.mulRight (RatFunc F) y) = c ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p
              (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c :=
  rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y c

end GaloisForLFunctions.HTGeometry.ABHN
