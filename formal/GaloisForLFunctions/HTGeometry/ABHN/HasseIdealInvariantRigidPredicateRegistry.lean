import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealMembership
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPowers
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDiscriminant

/-!
# Rigid ideal and algebra-invariant Hasse predicates

Ideal relations and fixed discriminant or trace data are reflected by every completion and by any
one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-! ## Ideal relations -/

def numberFieldIdealContainmentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I J : Ideal A) :=
  RigidHassePredicate.fixed
    (numberField_ideal_map_le_iff_forall_place K I J)
    (numberField_ideal_map_le_iff_exists_place K I J)

def rationalFunctionIdealContainmentRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_map_le_iff_forall_place F I J)
    (rationalFunction_ideal_map_le_iff_exists_place F I J)

def numberFieldIdealEqualityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I J : Ideal A) :=
  RigidHassePredicate.fixed
    (numberField_ideal_map_eq_iff_forall_place K I J)
    (numberField_ideal_map_eq_iff_exists_place K I J)

def rationalFunctionIdealEqualityRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_map_eq_iff_forall_place F I J)
    (rationalFunction_ideal_map_eq_iff_exists_place F I J)

def numberFieldIdealMembershipRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I : Ideal A) (a : A) :=
  RigidHassePredicate.fixed
    (numberField_ideal_mem_map_iff_forall_place K I a)
    (numberField_ideal_mem_map_iff_exists_place K I a)

def rationalFunctionIdealMembershipRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (a : A) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_mem_map_iff_forall_place F I a)
    (rationalFunction_ideal_mem_map_iff_exists_place F I a)

def numberFieldIdealPowerEqualityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I J : Ideal A) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_ideal_pow_eq_iff_forall_place K I J n)
    (numberField_ideal_pow_eq_iff_exists_place K I J n)

def rationalFunctionIdealPowerEqualityRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_pow_eq_iff_forall_place F I J n)
    (rationalFunction_ideal_pow_eq_iff_exists_place F I J n)

def numberFieldIdealIdempotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I : Ideal A) :=
  RigidHassePredicate.fixed
    (numberField_ideal_isIdempotentElem_iff_forall_place K I)
    (numberField_ideal_isIdempotentElem_iff_exists_place K I)

def rationalFunctionIdealIdempotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_isIdempotentElem_iff_forall_place F I)
    (rationalFunction_ideal_isIdempotentElem_iff_exists_place F I)

def numberFieldIdealNilpotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] (I : Ideal A) :=
  RigidHassePredicate.fixed
    (numberField_ideal_isNilpotent_iff_forall_place K I)
    (numberField_ideal_isNilpotent_iff_exists_place K I)

def rationalFunctionIdealNilpotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :=
  RigidHassePredicate.fixed
    (rationalFunction_ideal_isNilpotent_iff_forall_place F I)
    (rationalFunction_ideal_isNilpotent_iff_exists_place F I)

/-! ## Discriminant and trace -/

def numberFieldAlgebraDiscriminantRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (B : Type w)
    [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) (c : K) :=
  RigidHassePredicate.fixed
    (numberField_algebra_discr_eq_iff_forall_place K e c)
    (numberField_algebra_discr_eq_iff_exists_place K e c)

def rationalFunctionAlgebraDiscriminantRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (B : Type w)
    [CommRing B] [Algebra (RatFunc F) B] [Module.Free (RatFunc F) B]
    [Module.Finite (RatFunc F) B] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι (RatFunc F) B) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_discr_eq_iff_forall_place F e c)
    (rationalFunction_algebra_discr_eq_iff_exists_place F e c)

def numberFieldAlgebraDiscriminantNonzeroRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (B : Type w)
    [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) :=
  RigidHassePredicate.fixed
    (numberField_algebra_discr_ne_zero_iff_forall_place K e)
    (numberField_algebra_discr_ne_zero_iff_exists_place K e)

def rationalFunctionAlgebraDiscriminantNonzeroRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (B : Type w)
    [CommRing B] [Algebra (RatFunc F) B] [Module.Free (RatFunc F) B]
    [Module.Finite (RatFunc F) B] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι (RatFunc F) B) :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_discr_ne_zero_iff_forall_place F e)
    (rationalFunction_algebra_discr_ne_zero_iff_exists_place F e)

def numberFieldAlgebraTraceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (B : Type w)
    [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (x : B) (c : K) :=
  RigidHassePredicate.fixed
    (numberField_algebra_trace_eq_iff_forall_place K x c)
    (numberField_algebra_trace_eq_iff_exists_place K x c)

def rationalFunctionAlgebraTraceRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (B : Type w)
    [CommRing B] [Algebra (RatFunc F) B] [Module.Free (RatFunc F) B]
    [Module.Finite (RatFunc F) B] (x : B) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_trace_eq_iff_forall_place F x c)
    (rationalFunction_algebra_trace_eq_iff_exists_place F x c)

end GaloisForLFunctions.HTGeometry.ABHN
