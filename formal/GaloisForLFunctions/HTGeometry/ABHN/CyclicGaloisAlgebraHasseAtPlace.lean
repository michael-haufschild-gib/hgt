/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseLocalGlobal
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIdempotents
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraNilpotence
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraPolynomialRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutativity

/-!
# One-place Hasse descent for cyclic Galois-algebra elements

For every fixed element, polynomial relation, or one-sided division equation in a nonzero cyclic
Galois algebra, every completion is faithfully flat.  Consequently its unit, zero-divisor,
idempotence, nilpotence, polynomial, commutativity, and division behavior at any selected
completion is equivalent to its global behavior.  This is stronger than an all-place test, but
does not patch independently chosen local elements.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A fixed element of a nonzero cyclic Galois algebra over a number field is a unit exactly
when its image is a unit at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_isUnit_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    IsUnit x ↔ IsUnit (numberFieldLocalScalarExtensionMap K p
      (cyclicGaloisAlgebraCSA K L a ha) x) := by
  exact scalarExtensionMap_isUnit_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` is a unit exactly when its
image is a unit at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isUnit_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsUnit x ↔ IsUnit (rationalFunctionLocalScalarExtensionMap F p
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) := by
  exact scalarExtensionMap_isUnit_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over a number field is idempotent exactly
when its image is idempotent at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_isIdempotent_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    IsIdempotentElem x ↔ IsIdempotentElem (numberFieldLocalScalarExtensionMap K p
      (cyclicGaloisAlgebraCSA K L a ha) x) := by
  exact scalarExtensionMap_isIdempotent_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` is idempotent exactly when
its image is idempotent at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsIdempotentElem x ↔ IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) := by
  exact scalarExtensionMap_isIdempotent_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over a number field is nilpotent exactly
when its image is nilpotent at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_isNilpotent_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    IsNilpotent x ↔ IsNilpotent (numberFieldLocalScalarExtensionMap K p
      (cyclicGaloisAlgebraCSA K L a ha) x) := by
  exact scalarExtensionMap_isNilpotent_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed element of a nonzero cyclic Galois algebra over `F(t)` is nilpotent exactly when its
image is nilpotent at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    IsNilpotent x ↔ IsNilpotent (rationalFunctionLocalScalarExtensionMap F p
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) := by
  exact scalarExtensionMap_isNilpotent_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A polynomial relation for a fixed cyclic Galois-algebra element over a number field holds
globally exactly when it holds at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K) (f : Polynomial K)
    (x : cyclicGaloisAlgebra K L a) :
    f.eval₂ (algebraMap K (cyclicGaloisAlgebra K L a)) x = 0 ↔
      (f.map (algebraMap K (completion K p))).eval₂
          (algebraMap (completion K p)
            (completion K p ⊗[K] cyclicGaloisAlgebra K L a))
          (numberFieldLocalScalarExtensionMap K p
            (cyclicGaloisAlgebraCSA K L a ha) x) = 0 := by
  exact scalarExtensionMap_polynomial_eval₂_eq_zero_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) f x

/-- A polynomial relation for a fixed cyclic Galois-algebra element over `F(t)` holds globally
exactly when it holds at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (f : Polynomial (RatFunc F)) (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    f.eval₂ (algebraMap (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a)) x = 0 ↔
      (f.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).eval₂
          (algebraMap (rationalFunctionCompletion F p)
            (rationalFunctionCompletion F p ⊗[RatFunc F]
              cyclicGaloisAlgebra (RatFunc F) L a))
          (rationalFunctionLocalScalarExtensionMap F p
            (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x) = 0 := by
  exact scalarExtensionMap_polynomial_eval₂_eq_zero_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) f x

/-- A cyclic Galois algebra over a number field is commutative exactly when its scalar extension
is commutative at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_mul_comm_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (p : NumberFieldPlace K) :
    (∀ x y : cyclicGaloisAlgebra K L a, x * y = y * x) ↔
      ∀ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a, x * y = y * x := by
  exact tensorProduct_mul_comm_iff

/-- A cyclic Galois algebra over `F(t)` is commutative exactly when its scalar extension is
commutative at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_mul_comm_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (p : RationalFunctionPlace F) :
    (∀ x y : cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x) ↔
      ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
        cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x := by
  exact tensorProduct_mul_comm_iff

/-- Local commutativity at one specified number-field completion forces a nonzero cyclic Galois
Brauer class to be split.  The converse is deliberately not asserted: split matrix algebras can
still be noncommutative. -/
theorem numberField_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (h : ∀ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a, x * y = y * x) :
    brauerClass (cyclicGaloisAlgebraCSA K L a ha) = brauerSplitClass K := by
  apply csa_brauerClass_eq_split_of_mul_comm (cyclicGaloisAlgebraCSA K L a ha)
  exact (numberField_cyclicGaloisAlgebra_mul_comm_iff_at_place K L a p).mpr h

/-- Local commutativity at one specified `F(t)` completion forces a nonzero cyclic Galois Brauer
class to be split.  Splitness does not conversely force commutativity. -/
theorem rationalFunction_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (h : ∀ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a, x * y = y * x) :
    brauerClass (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) =
      brauerSplitClass (RatFunc F) := by
  apply csa_brauerClass_eq_split_of_mul_comm
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha)
  exact (rationalFunction_cyclicGaloisAlgebra_mul_comm_iff_at_place F L a p).mpr h

/-- A non-split cyclic Galois Brauer class over a number field has a noncommuting pair at every
completion. -/
theorem numberField_cyclicGaloisAlgebra_forall_local_noncommuting_of_brauerClass_ne_split
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0)
    (h : brauerClass (cyclicGaloisAlgebraCSA K L a ha) ≠ brauerSplitClass K) :
    ∀ p : NumberFieldPlace K, ∃ x y : completion K p ⊗[K] cyclicGaloisAlgebra K L a,
      x * y ≠ y * x := by
  intro p
  by_contra hlocal
  push Not at hlocal
  exact h (numberField_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm_at_place
    K L a ha p hlocal)

/-- A non-split cyclic Galois Brauer class over `F(t)` has a noncommuting pair at every finite
and infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_forall_local_noncommuting_of_brauerClass_ne_split
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0)
    (h : brauerClass (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) ≠
      brauerSplitClass (RatFunc F)) :
    ∀ p : RationalFunctionPlace F,
      ∃ x y : rationalFunctionCompletion F p ⊗[RatFunc F]
        cyclicGaloisAlgebra (RatFunc F) L a, x * y ≠ y * x := by
  intro p
  by_contra hlocal
  push Not at hlocal
  exact h (rationalFunction_cyclicGaloisAlgebra_brauerClass_eq_split_of_local_mul_comm_at_place
    F L a ha p hlocal)

/-- A fixed number-field cyclic Galois-algebra element has a nonzero left annihilator exactly
when its image has one at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed number-field cyclic Galois-algebra element has a nonzero right annihilator exactly
when its image has one at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x : cyclicGaloisAlgebra K L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∃ z, z ≠ 0 ∧
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x

/-- A fixed global-function-field cyclic Galois-algebra element has a nonzero left annihilator
exactly when its image has one at any specified completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ x * y = 0) ↔ ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulLeft_eq_zero_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed global-function-field cyclic Galois-algebra element has a nonzero right annihilator
exactly when its image has one at any specified completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ y, y ≠ 0 ∧ y * x = 0) ↔ ∃ z, z ≠ 0 ∧
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x = 0 := by
  exact scalarExtensionMap_exists_nonzero_mulRight_eq_zero_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x

/-- A fixed left-division equation in a nonzero cyclic Galois algebra over a number field is
solvable globally exactly when it is solvable at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, x * z = y) ↔ ∃ z,
      numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x * z =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y := by
  exact scalarExtensionMap_exists_mulLeft_eq_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A fixed right-division equation in a nonzero cyclic Galois algebra over a number field is
solvable globally exactly when it is solvable at any specified completion. -/
theorem numberField_cyclicGaloisAlgebra_exists_mulRight_eq_iff_at_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) (p : NumberFieldPlace K)
    (x y : cyclicGaloisAlgebra K L a) :
    (∃ z, z * x = y) ↔ ∃ z,
      z * numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) x =
        numberFieldLocalScalarExtensionMap K p (cyclicGaloisAlgebraCSA K L a ha) y := by
  exact scalarExtensionMap_exists_mulRight_eq_iff
    (L := completion K p) (cyclicGaloisAlgebraCSA K L a ha) x y

/-- A fixed left-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable
globally exactly when it is solvable at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, x * z = y) ↔ ∃ z,
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x * z =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y := by
  exact scalarExtensionMap_exists_mulLeft_eq_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

/-- A fixed right-division equation in a nonzero cyclic Galois algebra over `F(t)` is solvable
globally exactly when it is solvable at any specified finite or infinite completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_exists_mulRight_eq_iff_at_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) (p : RationalFunctionPlace F)
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) :
    (∃ z, z * x = y) ↔ ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x =
      rationalFunctionLocalScalarExtensionMap F p
        (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) y := by
  exact scalarExtensionMap_exists_mulRight_eq_iff
    (L := rationalFunctionCompletion F p)
    (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y

end GaloisForLFunctions.HTGeometry.ABHN
