import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseMorphisms
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.AlgebraHomFailureHasse

/-!
# Rigid Hasse predicates for cyclic-algebra morphisms

Equality and composition of cyclic-algebra morphisms, automorphism equality, map-theoretic
properties, and the Azumaya condition are reflected by completion at every or any one place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-! ## Number fields -/

section NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

def numberFieldCyclicAlgebraAlgHomEqualityRigidHassePredicate
    (a : K) (f g : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algHom_eq_iff_forall_place K L a f g)
    (numberField_algHom_eq_iff_exists_place K f g)

def numberFieldCyclicAlgebraAlgHomCompositionRigidHassePredicate
    (a : K) (f g h : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algHom_comp_eq_iff_forall_place K L a f g h)
    (numberField_algHom_comp_eq_iff_exists_place K f g h)

def numberFieldCyclicAlgebraAlgEquivEqualityRigidHassePredicate
    (a : K) (e f : cyclicGaloisAlgebra K L a ≃ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algEquiv_eq_iff_forall_place K L a e f)
    (numberField_algEquiv_eq_iff_exists_place K e f)

def numberFieldCyclicAlgebraAlgHomInjectiveRigidHassePredicate
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algHom_injective_iff_forall_place K L a f)
    (numberField_cyclicGaloisAlgebra_algHom_injective_iff_exists_place K L a f)

def numberFieldCyclicAlgebraAlgHomSurjectiveRigidHassePredicate
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algHom_surjective_iff_forall_place K L a f)
    (numberField_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place K L a f)

def numberFieldCyclicAlgebraAlgHomBijectiveRigidHassePredicate
    (a : K) (f : cyclicGaloisAlgebra K L a →ₐ[K] cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_algHom_bijective_iff_forall_place K L a f)
    (numberField_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place K L a f)

def numberFieldCyclicAlgebraAzumayaRigidHassePredicate (a : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_isAzumaya_iff_forall_place K L a)
    (numberField_cyclicGaloisAlgebra_isAzumaya_iff_exists_place K L a)

end NumberField

/-! ## Rational function fields -/

section RationalFunction

variable (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
  [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]

def rationalFunctionCyclicAlgebraAlgHomEqualityRigidHassePredicate
    (a : RatFunc F)
    (f g : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algHom_eq_iff_forall_place F L a f g)
    (rationalFunction_algHom_eq_iff_exists_place F f g)

def rationalFunctionCyclicAlgebraAlgHomCompositionRigidHassePredicate
    (a : RatFunc F)
    (f g h : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algHom_comp_eq_iff_forall_place F L a f g h)
    (rationalFunction_algHom_comp_eq_iff_exists_place F f g h)

def rationalFunctionCyclicAlgebraAlgEquivEqualityRigidHassePredicate
    (a : RatFunc F)
    (e f : cyclicGaloisAlgebra (RatFunc F) L a ≃ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algEquiv_eq_iff_forall_place F L a e f)
    (rationalFunction_algEquiv_eq_iff_exists_place F e f)

def rationalFunctionCyclicAlgebraAlgHomInjectiveRigidHassePredicate
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algHom_injective_iff_forall_place F L a f)
    (rationalFunction_cyclicGaloisAlgebra_algHom_injective_iff_exists_place F L a f)

def rationalFunctionCyclicAlgebraAlgHomSurjectiveRigidHassePredicate
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algHom_surjective_iff_forall_place F L a f)
    (rationalFunction_cyclicGaloisAlgebra_algHom_surjective_iff_exists_place F L a f)

def rationalFunctionCyclicAlgebraAlgHomBijectiveRigidHassePredicate
    (a : RatFunc F)
    (f : cyclicGaloisAlgebra (RatFunc F) L a →ₐ[RatFunc F]
      cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_algHom_bijective_iff_forall_place F L a f)
    (rationalFunction_cyclicGaloisAlgebra_algHom_bijective_iff_exists_place F L a f)

def rationalFunctionCyclicAlgebraAzumayaRigidHassePredicate (a : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_forall_place F L a)
    (rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_exists_place F L a)

end RationalFunction

end GaloisForLFunctions.HTGeometry.ABHN
