import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraPolynomialRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseFreeAlgebraEvaluation
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialDivisibility

/-!
# Polynomial-relation failures at every completion

Faithful scalar extension reflects prescribed commutative and noncommutative polynomial
relations. Consequently, failure of such a relation over a global field persists at every
completion. These results concern fixed global coefficients and elements; they do not glue
independently chosen local data.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Failure of a fixed noncommutative polynomial identity in a number-field CSA persists at every
completion. -/
theorem numberFieldFreeAlgebra_lift_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra K X) (c : A.carrier) :
    FreeAlgebra.lift K x P ≠ c ↔ ∀ p : NumberFieldPlace K,
      FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P ≠
        numberFieldLocalScalarExtensionMap K p A c :=
  not_iff_forall_not_of_iff_exists
    (numberFieldFreeAlgebra_lift_eq_iff_exists_place K A X x P c)

/-- Failure of a fixed noncommutative polynomial identity in an `F(t)`-CSA persists at every
completion. -/
theorem rationalFunctionFreeAlgebra_lift_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) (c : A.carrier) :
    FreeAlgebra.lift (RatFunc F) x P ≠ c ↔ ∀ p : RationalFunctionPlace F,
      FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P ≠
          rationalFunctionLocalScalarExtensionMap F p A c :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionFreeAlgebra_lift_eq_iff_exists_place F A X x P c)

/-- Noninvertibility of a fixed noncommutative polynomial value in a number-field CSA persists at
every completion. -/
theorem numberFieldFreeAlgebra_lift_not_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (X : Type w) (x : X → A.carrier) (P : FreeAlgebra K X) :
    ¬ IsUnit (FreeAlgebra.lift K x P) ↔ ∀ p : NumberFieldPlace K,
      ¬ IsUnit
        (FreeAlgebra.lift K (fun i => numberFieldLocalScalarExtensionMap K p A (x i)) P) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldFreeAlgebra_lift_isUnit_iff_exists_place K A X x P)

/-- Noninvertibility of a fixed noncommutative polynomial value in an `F(t)`-CSA persists at every
completion. -/
theorem rationalFunctionFreeAlgebra_lift_not_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (X : Type w) (x : X → A.carrier)
    (P : FreeAlgebra (RatFunc F) X) :
    ¬ IsUnit (FreeAlgebra.lift (RatFunc F) x P) ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsUnit (FreeAlgebra.lift (RatFunc F)
        (fun i => rationalFunctionLocalScalarExtensionMap F p A (x i)) P) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionFreeAlgebra_lift_isUnit_iff_exists_place F A X x P)

/-- Failure of a polynomial relation for a fixed number-field CSA element persists at every
completion. -/
theorem numberFieldLocalScalarExtensionMap_polynomial_eval₂_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K)
    (p : Polynomial K) (a : A.carrier) :
    p.eval₂ (algebraMap K A.carrier) a ≠ 0 ↔ ∀ q : NumberFieldPlace K,
      (p.map (algebraMap K (completion K q))).eval₂
        (algebraMap (completion K q) (completion K q ⊗[K] A.carrier))
          (numberFieldLocalScalarExtensionMap K q A a) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place K A p a)

/-- Failure of a polynomial relation for a fixed function-field CSA element persists at every
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F))
    (p : Polynomial (RatFunc F)) (a : A.carrier) :
    p.eval₂ (algebraMap (RatFunc F) A.carrier) a ≠ 0 ↔
      ∀ q : RationalFunctionPlace F,
        (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F q))).eval₂
          (algebraMap (rationalFunctionCompletion F q)
            (rationalFunctionCompletion F q ⊗[RatFunc F] A.carrier))
              (rationalFunctionLocalScalarExtensionMap F q A a) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place F A p a)

/-- Failure of a prescribed monic factor over a number field persists at every completion. -/
theorem numberFieldPolynomial_not_dvd_iff_forall_place_of_monic
    (K : Type u) [Field K] [NumberField K] (p q : Polynomial K) (hp : p.Monic) :
    ¬ (p ∣ q) ↔ ∀ v : NumberFieldPlace K,
      ¬ (p.map (algebraMap K (completion K v)) ∣
        q.map (algebraMap K (completion K v))) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldPolynomial_dvd_iff_exists_place_of_monic K p q hp)

/-- Failure of a prescribed monic factor over `F(t)` persists at every completion. -/
theorem rationalFunctionPolynomial_not_dvd_iff_forall_place_of_monic
    (F : Type u) [Field F] [Finite F]
    (p q : Polynomial (RatFunc F)) (hp : p.Monic) :
    ¬ (p ∣ q) ↔ ∀ v : RationalFunctionPlace F,
      ¬ (p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) ∣
        q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v))) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionPolynomial_dvd_iff_exists_place_of_monic F p q hp)

end GaloisForLFunctions.HTGeometry.ABHN
