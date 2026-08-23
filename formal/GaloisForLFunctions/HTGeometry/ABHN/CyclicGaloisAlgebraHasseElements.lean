/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseStructure
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutativity
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIdempotents
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraPolynomialRelations

/-!
# Hasse element tests and a local obstruction for cyclic Galois algebras

Nonzero cyclic Galois algebras inherit completionwise tests for idempotents and nilpotents.
These are fixed-global-element assertions.  In addition, a non-split cyclic Brauer class has a
noncommuting pair after scalar extension at some completion.  This obstruction does not
characterize splitting: a split matrix algebra of degree greater than one is still
noncommutative.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- Idempotence in a nonzero cyclic Galois algebra over a number field is detected at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_isIdempotent_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    IsIdempotentElem x ↔ ∀ p : NumberFieldPlace K,
      IsIdempotentElem (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  numberFieldLocalScalarExtensionMap_isIdempotent_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Idempotence in a nonzero cyclic Galois algebra over a global function field is detected at
every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsIdempotentElem x ↔ ∀ p : RationalFunctionPlace F,
      IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- Idempotence in a nonzero cyclic Galois algebra over a number field can be certified at one
completion. -/
theorem numberField_cyclicGaloisAlgebra_isIdempotent_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    IsIdempotentElem x ↔ ∃ p : NumberFieldPlace K,
      IsIdempotentElem (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  numberFieldLocalScalarExtensionMap_isIdempotent_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Idempotence in a nonzero cyclic Galois algebra over a global function field can be certified
at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsIdempotentElem x ↔ ∃ p : RationalFunctionPlace F,
      IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- Nilpotence in a nonzero cyclic Galois algebra over a number field is detected at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_isNilpotent_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    IsNilpotent x ↔ ∀ p : NumberFieldPlace K,
      IsNilpotent (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  numberFieldLocalScalarExtensionMap_isNilpotent_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Nilpotence in a nonzero cyclic Galois algebra over a global function field is detected at
every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsNilpotent x ↔ ∀ p : RationalFunctionPlace F,
      IsNilpotent (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- Nilpotence in a nonzero cyclic Galois algebra over a number field can be certified at one
completion. -/
theorem numberField_cyclicGaloisAlgebra_isNilpotent_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :
    IsNilpotent x ↔ ∃ p : NumberFieldPlace K,
      IsNilpotent (numberFieldLocalScalarExtensionMap K p
        (cyclicGaloisAlgebraCSA K L a ha) x) :=
  numberFieldLocalScalarExtensionMap_isNilpotent_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) x

/-- Nilpotence in a nonzero cyclic Galois algebra over a global function field can be certified
at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsNilpotent x ↔ ∃ p : RationalFunctionPlace F,
      IsNilpotent (rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) :=
  rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A nonzero cyclic Galois algebra over a number field is commutative exactly when every
completed scalar extension is commutative. -/
theorem numberField_cyclicGaloisAlgebra_mul_comm_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) :
    (∀ x y : cyclicGaloisAlgebra K L a, x * y = y * x) ↔
      ∀ p : NumberFieldPlace K, ∀ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a,
        x * y = y * x :=
  numberFieldLocalScalarExtensionMap_mul_comm_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha)

/-- A nonzero cyclic Galois algebra over a global function field is commutative exactly when
every completed scalar extension is commutative. -/
theorem rationalFunction_cyclicGaloisAlgebra_mul_comm_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) :
    (∀ x y : cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x) ↔
      ∀ p : RationalFunctionPlace F,
        ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
          cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x :=
  rationalFunctionLocalScalarExtensionMap_mul_comm_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha)

/-- If every completed scalar extension of a nonzero cyclic Galois algebra over a number field
is commutative, its Brauer class is split. -/
theorem numberField_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0)
    (h : ∀ p : NumberFieldPlace K, ∀ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a,
      x * y = y * x) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) = brauerSplitClass K :=
  numberField_brauerClass_eq_split_of_local_mul_comm K
    (cyclicGaloisAlgebraCSA K L a ha) h

/-- If every completed scalar extension of a nonzero cyclic Galois algebra over a global
function field is commutative, its Brauer class is split. -/
theorem rationalFunction_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0)
    (h : ∀ p : RationalFunctionPlace F,
      ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
        cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x) :
    brauerClass (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) =
      brauerSplitClass (RatFunc F) :=
  rationalFunction_brauerClass_eq_split_of_local_mul_comm F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) h

/-- A non-split cyclic Galois Brauer class over a number field has a noncommuting pair after
scalar extension at some completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_local_noncommuting_of_brauerClass_ne_split
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0)
    (h : brauerClass (cyclicGaloisAlgebraCSA K L a ha) ≠ brauerSplitClass K) :
    ∃ p : NumberFieldPlace K, ∃ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a,
      x * y ≠ y * x :=
  numberField_exists_local_noncommuting_of_brauerClass_ne_split K
    (cyclicGaloisAlgebraCSA K L a ha) h

/-- A non-split cyclic Galois Brauer class over a global function field has a noncommuting pair
after scalar extension at some completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_local_noncommuting_of_brauerClass_ne_split
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0)
    (h : brauerClass (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) ≠
      brauerSplitClass (RatFunc F)) :
    ∃ p : RationalFunctionPlace F,
      ∃ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
        cyclicGaloisAlgebra (RatFunc F) L a, x * y ≠ y * x :=
  rationalFunction_exists_local_noncommuting_of_brauerClass_ne_split F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) h

/-- A polynomial relation for a fixed element of a nonzero cyclic Galois algebra over a number
field holds exactly when it holds at every completion. -/
theorem numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : Polynomial K) (x : cyclicGaloisAlgebra K L a) :
    p.eval₂ (algebraMap K (cyclicGaloisAlgebra K L a)) x = 0 ↔
      ∀ v : NumberFieldPlace K,
        (p.map (algebraMap K (completion K v))).eval₂
          (algebraMap (completion K v)
            (completion K v ⊗[K] cyclicGaloisAlgebra K L a))
          (numberFieldLocalScalarExtensionMap K v
            (cyclicGaloisAlgebraCSA K L a ha) x) = 0 :=
  numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place K
    (cyclicGaloisAlgebraCSA K L a ha) p x

/-- A polynomial relation for a fixed element of a nonzero cyclic Galois algebra over a global
function field holds exactly when it holds at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : Polynomial (RatFunc F))
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    p.eval₂ (algebraMap (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)) x = 0 ↔
      ∀ v : RationalFunctionPlace F,
        (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).eval₂
          (algebraMap (rationalFunctionCompletion F v)
            (rationalFunctionCompletion F v ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a))
          (rationalFunctionLocalScalarExtensionMap F v
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) = 0 :=
  rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) p x

/-- A polynomial relation for a fixed element of a nonzero cyclic Galois algebra over a number
field can be certified at one completion. -/
theorem numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : Polynomial K) (x : cyclicGaloisAlgebra K L a) :
    p.eval₂ (algebraMap K (cyclicGaloisAlgebra K L a)) x = 0 ↔
      ∃ v : NumberFieldPlace K,
        (p.map (algebraMap K (completion K v))).eval₂
          (algebraMap (completion K v)
            (completion K v ⊗[K] cyclicGaloisAlgebra K L a))
          (numberFieldLocalScalarExtensionMap K v
            (cyclicGaloisAlgebraCSA K L a ha) x) = 0 :=
  numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place K
    (cyclicGaloisAlgebraCSA K L a ha) p x

/-- A polynomial relation for a fixed element of a nonzero cyclic Galois algebra over a global
function field can be certified at one completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : Polynomial (RatFunc F))
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    p.eval₂ (algebraMap (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)) x = 0 ↔
      ∃ v : RationalFunctionPlace F,
        (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))).eval₂
          (algebraMap (rationalFunctionCompletion F v)
            (rationalFunctionCompletion F v ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a))
          (rationalFunctionLocalScalarExtensionMap F v
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) = 0 :=
  rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place F
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) p x

end GaloisForLFunctions.HTGeometry.ABHN
