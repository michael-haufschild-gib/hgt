import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraPolynomialRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularCharpolySeparable
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariantValues
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerInvariants

/-!
# Rigid central-simple-algebra spectral Hasse predicates

Polynomial relations and regular-representation invariants of fixed central-simple-algebra elements
are reflected by every completion and by any one completion.  The same rigidity applies to the
Sylvester operator attached to a fixed pair of algebra elements.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-! ## Polynomial and regular-representation data -/

def numberFieldCSAPolynomialRelationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (p : Polynomial K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place K A p a)
    (numberFieldLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place K A p a)

def rationalFunctionCSAPolynomialRelationRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (p : Polynomial (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_forall_place F A p a)
    (rationalFunctionLocalScalarExtensionMap_polynomial_eval₂_eq_zero_iff_exists_place F A p a)

def numberFieldCSARegularCharpolySeparableRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberField_regularCharpoly_separable_iff_forall_place K A a)
    (numberField_regularCharpoly_separable_iff_exists_place K A a)

def rationalFunctionCSARegularCharpolySeparableRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunction_regularCharpoly_separable_iff_forall_place F A a)
    (rationalFunction_regularCharpoly_separable_iff_exists_place F A a)

def numberFieldCSARegularCharpolyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (p : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberField_regularCharpoly_eq_iff_forall_place K A a p)
    (numberField_regularCharpoly_eq_iff_exists_place K A a p)

def rationalFunctionCSARegularCharpolyRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (p : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunction_regularCharpoly_eq_iff_forall_place F A a p)
    (rationalFunction_regularCharpoly_eq_iff_exists_place F A a p)

def numberFieldCSARegularTraceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (c : K) :=
  RigidHassePredicate.fixed
    (numberField_regularTrace_eq_iff_forall_place K A a c)
    (numberField_regularTrace_eq_iff_exists_place K A a c)

def rationalFunctionCSARegularTraceRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_regularTrace_eq_iff_forall_place F A a c)
    (rationalFunction_regularTrace_eq_iff_exists_place F A a c)

def numberFieldCSARegularNormRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a : A.carrier) (c : K) :=
  RigidHassePredicate.fixed
    (numberField_regularNorm_eq_iff_forall_place K A a c)
    (numberField_regularNorm_eq_iff_exists_place K A a c)

def rationalFunctionCSARegularNormRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_regularNorm_eq_iff_forall_place F A a c)
    (rationalFunction_regularNorm_eq_iff_exists_place F A a c)

/-! ## Sylvester-operator data -/

def numberFieldCSAIntertwinerCharpolyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a b : A.carrier) (q : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place K A a b q)
    (numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place K A a b q)

def rationalFunctionCSAIntertwinerCharpolyRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (q : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place F A a b q)
    (rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place F A a b q)

def numberFieldCSAIntertwinerTraceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a b : A.carrier) (c : K) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place K A a b c)
    (numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place K A a b c)

def rationalFunctionCSAIntertwinerTraceRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place F A a b c)
    (rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place F A a b c)

def numberFieldCSAIntertwinerDetRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a b : A.carrier) (c : K) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place K A a b c)
    (numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place K A a b c)

def rationalFunctionCSAIntertwinerDetRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place F A a b c)
    (rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place F A a b c)

end GaloisForLFunctions.HTGeometry.ABHN
