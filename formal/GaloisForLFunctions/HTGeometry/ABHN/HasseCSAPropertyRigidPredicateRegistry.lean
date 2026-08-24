import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIdempotents
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraNilpotence
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCenter
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutativity
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple
import GaloisForLFunctions.HTGeometry.ABHN.HasseAzumaya

/-!
# Rigid central-simple-algebra property Hasse predicates

Elementwise properties and finite-dimensional algebra structure are reflected by every completion
and by any one completion.  In particular, central simplicity and the Azumaya condition are exposed
through the same reusable rigid Hasse interface.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-! ## Elementwise and algebra-wide properties -/

def numberFieldCSAIdempotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_isIdempotent_iff_forall_place K A a)
    (numberFieldLocalScalarExtensionMap_isIdempotent_iff_exists_place K A a)

def rationalFunctionCSAIdempotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_forall_place F A a)
    (rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_exists_place F A a)

def numberFieldCSANilpotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_isNilpotent_iff_forall_place K A a)
    (numberFieldLocalScalarExtensionMap_isNilpotent_iff_exists_place K A a)

def rationalFunctionCSANilpotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_forall_place F A a)
    (rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_exists_place F A a)

def numberFieldCSAUnitRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place K A a)
    (numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place K A a)

def rationalFunctionCSAUnitRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place F A a)
    (rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place F A a)

def numberFieldCSACentralElementRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mem_center_iff_forall_place K A a)
    (numberFieldLocalScalarExtensionMap_mem_center_iff_exists_place K A a)

def rationalFunctionCSACentralElementRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mem_center_iff_forall_place F A a)
    (rationalFunctionLocalScalarExtensionMap_mem_center_iff_exists_place F A a)

def numberFieldCSACommutativeRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mul_comm_iff_forall_place K A)
    (numberFieldLocalScalarExtensionMap_mul_comm_iff_exists_place K A)

def rationalFunctionCSACommutativeRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_forall_place F A)
    (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_exists_place F A)

/-! ## Simple, central-simple, and Azumaya structure -/

def numberFieldSimpleAlgebraRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :=
  RigidHassePredicate.fixed
    (numberField_isSimpleRing_iff_forall_place K (A := A))
    (numberField_isSimpleRing_iff_exists_place K (A := A))

def rationalFunctionSimpleAlgebraRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [Ring A] [Algebra (RatFunc F) A] [Algebra.IsCentral (RatFunc F) A]
    [Module.Finite (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_isSimpleRing_iff_forall_place F (A := A))
    (rationalFunction_isSimpleRing_iff_exists_place F (A := A))

def numberFieldCentralSimpleAlgebraRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [Ring A] [Algebra K A] [Module.Finite K A] :=
  RigidHassePredicate.fixed
    (numberField_isCentral_and_isSimpleRing_iff_forall_place K (A := A))
    (numberField_isCentral_and_isSimpleRing_iff_exists_place K (A := A))

def rationalFunctionCentralSimpleAlgebraRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_isCentral_and_isSimpleRing_iff_forall_place F (A := A))
    (rationalFunction_isCentral_and_isSimpleRing_iff_exists_place F (A := A))

def numberFieldAzumayaAlgebraRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [Ring A] [Algebra K A] [Module.Finite K A] :=
  RigidHassePredicate.fixed
    (numberField_isAzumaya_iff_forall_place K (A := A))
    (numberField_isAzumaya_iff_exists_place K (A := A))

def rationalFunctionAzumayaAlgebraRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_isAzumaya_iff_forall_place F (A := A))
    (rationalFunction_isAzumaya_iff_exists_place F (A := A))

end GaloisForLFunctions.HTGeometry.ABHN
