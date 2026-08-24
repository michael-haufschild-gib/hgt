import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseFreeAlgebraEvaluation

/-!
# Rigid free-algebra Hasse predicates

Evaluation identities and invertibility of fixed noncommutative polynomial values in central simple
algebras are reflected by every completion and by any one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

def numberFieldFreeAlgebraEvaluationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (X : Type v) (x : X → A.carrier) (P : FreeAlgebra K X) (c : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldFreeAlgebra_lift_eq_iff_forall_place K A X x P c)
    (numberFieldFreeAlgebra_lift_eq_iff_exists_place K A X x P c)

def rationalFunctionFreeAlgebraEvaluationRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (X : Type v) (x : X → A.carrier) (P : FreeAlgebra (RatFunc F) X) (c : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionFreeAlgebra_lift_eq_iff_forall_place F A X x P c)
    (rationalFunctionFreeAlgebra_lift_eq_iff_exists_place F A X x P c)

def numberFieldFreeAlgebraEvaluationUnitRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (X : Type v) (x : X → A.carrier) (P : FreeAlgebra K X) :=
  RigidHassePredicate.fixed
    (numberFieldFreeAlgebra_lift_isUnit_iff_forall_place K A X x P)
    (numberFieldFreeAlgebra_lift_isUnit_iff_exists_place K A X x P)

def rationalFunctionFreeAlgebraEvaluationUnitRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (X : Type v) (x : X → A.carrier) (P : FreeAlgebra (RatFunc F) X) :=
  RigidHassePredicate.fixed
    (rationalFunctionFreeAlgebra_lift_isUnit_iff_forall_place F A X x P)
    (rationalFunctionFreeAlgebra_lift_isUnit_iff_exists_place F A X x P)

end GaloisForLFunctions.HTGeometry.ABHN
