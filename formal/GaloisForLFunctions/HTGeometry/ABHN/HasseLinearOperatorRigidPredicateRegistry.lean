import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapSolvability
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapExactness
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapInvariants

/-!
# Rigid linear-operator Hasse predicates

Structural, solvability, exactness, and fixed spectral data for linear maps over global fields are
reflected by every completion and by any one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w z

/-! ## Structural and solvability predicates -/

def numberFieldLinearMapInjectiveRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  RigidHassePredicate.fixed
    (numberFieldLinearMap_injective_iff_forall_place K f)
    (numberFieldLinearMap_injective_iff_exists_place K f)

def rationalFunctionLinearMapInjectiveRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  RigidHassePredicate.fixed
    (rationalFunctionLinearMap_injective_iff_forall_place F f)
    (rationalFunctionLinearMap_injective_iff_exists_place F f)

def numberFieldLinearMapSurjectiveRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  RigidHassePredicate.fixed
    (numberFieldLinearMap_surjective_iff_forall_place K f)
    (numberFieldLinearMap_surjective_iff_exists_place K f)

def rationalFunctionLinearMapSurjectiveRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  RigidHassePredicate.fixed
    (rationalFunctionLinearMap_surjective_iff_forall_place F f)
    (rationalFunctionLinearMap_surjective_iff_exists_place F f)

def numberFieldLinearMapBijectiveRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  RigidHassePredicate.fixed
    (numberFieldLinearMap_bijective_iff_forall_place K f)
    (numberFieldLinearMap_bijective_iff_exists_place K f)

def rationalFunctionLinearMapBijectiveRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  RigidHassePredicate.fixed
    (rationalFunctionLinearMap_bijective_iff_forall_place F f)
    (rationalFunctionLinearMap_bijective_iff_exists_place F f)

def numberFieldLinearMapSolvabilityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (y : N) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_exists_preimage_iff_forall_place K f y)
    (numberField_linearMap_exists_preimage_iff_exists_place K f y)

def rationalFunctionLinearMapSolvabilityRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (y : N) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_exists_preimage_iff_forall_place F f y)
    (rationalFunction_linearMap_exists_preimage_iff_exists_place F f y)

def numberFieldLinearMapExactRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) (P : Type z)
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P) :=
  RigidHassePredicate.fixed
    (numberFieldLinearMap_exact_iff_forall_place K f g)
    (numberFieldLinearMap_exact_iff_exists_place K f g)

def rationalFunctionLinearMapExactRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) (P : Type z)
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    [AddCommGroup P] [Module (RatFunc F) P]
    (f : M →ₗ[RatFunc F] N) (g : N →ₗ[RatFunc F] P) :=
  RigidHassePredicate.fixed
    (rationalFunctionLinearMap_exact_iff_forall_place F f g)
    (rationalFunctionLinearMap_exact_iff_exists_place F f g)

/-! ## Fixed spectral invariants -/

def numberFieldLinearMapCharpolyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (p : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_charpoly_eq_iff_forall_place K f p)
    (numberField_linearMap_charpoly_eq_iff_exists_place K f p)

def rationalFunctionLinearMapCharpolyRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (p : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_charpoly_eq_iff_forall_place F f p)
    (rationalFunction_linearMap_charpoly_eq_iff_exists_place F f p)

def numberFieldLinearMapTraceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_trace_eq_iff_forall_place K f a)
    (numberField_linearMap_trace_eq_iff_exists_place K f a)

def rationalFunctionLinearMapTraceRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_trace_eq_iff_forall_place F f a)
    (rationalFunction_linearMap_trace_eq_iff_exists_place F f a)

def numberFieldLinearMapDeterminantRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_det_eq_iff_forall_place K f a)
    (numberField_linearMap_det_eq_iff_exists_place K f a)

def rationalFunctionLinearMapDeterminantRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_det_eq_iff_forall_place F f a)
    (rationalFunction_linearMap_det_eq_iff_exists_place F f a)

end GaloisForLFunctions.HTGeometry.ABHN
