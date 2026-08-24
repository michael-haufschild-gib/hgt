import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCenter
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEquations
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIdempotents

/-!
# Central-simple-algebra element failures at every completion

Fixed multiplication equations, centrality, and idempotence are reflected by every completed
scalar extension. Their failures therefore persist uniformly at all places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- Failure of a multiplication equation in a number-field CSA persists at every completion. -/
theorem numberFieldLocalScalarExtensionMap_mul_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a b c : A.carrier) :
    a * b ≠ c ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a *
        numberFieldLocalScalarExtensionMap K p A b ≠
          numberFieldLocalScalarExtensionMap K p A c :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_mul_eq_iff_exists_place K A a b c)

/-- Failure of a multiplication equation in an `F(t)`-CSA persists at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mul_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a b c : A.carrier) :
    a * b ≠ c ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a *
        rationalFunctionLocalScalarExtensionMap F p A b ≠
          rationalFunctionLocalScalarExtensionMap F p A c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_mul_eq_iff_exists_place F A a b c)

/-- Noncentrality of a fixed number-field CSA element persists at every completion. -/
theorem numberFieldLocalScalarExtensionMap_not_mem_center_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a : A.carrier) :
    a ∉ Subalgebra.center K A.carrier ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∉
        Subalgebra.center (completion K p) (completion K p ⊗[K] A.carrier) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_mem_center_iff_exists_place K A a)

/-- Noncentrality of a fixed `F(t)`-CSA element persists at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_not_mem_center_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    a ∉ Subalgebra.center (RatFunc F) A.carrier ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∉
        Subalgebra.center (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_mem_center_iff_exists_place F A a)

/-- Failure of idempotence for a number-field CSA element persists at every completion. -/
theorem numberFieldLocalScalarExtensionMap_not_isIdempotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) (a : A.carrier) :
    ¬ IsIdempotentElem a ↔ ∀ p : NumberFieldPlace K,
      ¬ IsIdempotentElem (numberFieldLocalScalarExtensionMap K p A a) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_isIdempotent_iff_exists_place K A a)

/-- Failure of idempotence for an `F(t)`-CSA element persists at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_not_isIdempotent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    ¬ IsIdempotentElem a ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p A a) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_exists_place F A a)

end GaloisForLFunctions.HTGeometry.ABHN
