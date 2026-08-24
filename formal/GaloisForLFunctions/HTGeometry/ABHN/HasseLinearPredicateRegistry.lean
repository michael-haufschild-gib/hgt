import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapCokernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleQuotients
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRanges
import GaloisForLFunctions.HTGeometry.ABHN.HasseSpanning
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleMembership
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence
import GaloisForLFunctions.HTGeometry.ABHN.HasseBasisFamily
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapInvariants

/-!
# Linear and submodule Hasse-predicate registry

Completionwise local--global predicates for finite-dimensional linear algebra over number fields
and rational function fields: exact mapping properties, kernel/range/cokernel dimensions,
generalized eigenspaces, submodules, spanning and basis families, and spectral invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-! ## Linear maps and dimensions -/

def numberFieldLinearMapSurjectiveHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  HassePredicate.fixed (numberFieldLinearMap_surjective_iff_forall_place K f)

def rationalFunctionLinearMapSurjectiveHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  HassePredicate.fixed (rationalFunctionLinearMap_surjective_iff_forall_place F f)

def numberFieldLinearMapBijectiveHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  HassePredicate.fixed (numberFieldLinearMap_bijective_iff_forall_place K f)

def rationalFunctionLinearMapBijectiveHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  HassePredicate.fixed (rationalFunctionLinearMap_bijective_iff_forall_place F f)

def numberFieldLinearMapKernelDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  HassePredicate.fixed (numberField_linearMap_ker_finrank_eq_iff_forall_place K f n)

def rationalFunctionLinearMapKernelDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_linearMap_ker_finrank_eq_iff_forall_place F f n)

def numberFieldLinearMapRangeDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  HassePredicate.fixed (numberField_linearMap_range_finrank_eq_iff_forall_place K f n)

def rationalFunctionLinearMapRangeDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_linearMap_range_finrank_eq_iff_forall_place F f n)

def numberFieldLinearMapCokernelDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  HassePredicate.fixed (numberField_linearMap_cokernel_finrank_eq_iff_forall_place K f n)

def rationalFunctionLinearMapCokernelDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_linearMap_cokernel_finrank_eq_iff_forall_place F f n)

def numberFieldLinearMapGeneralizedEigenspaceDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n d : ℕ) :=
  HassePredicate.fixed
    (numberField_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place K f a n d)

def rationalFunctionLinearMapGeneralizedEigenspaceDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) (n d : ℕ) :=
  HassePredicate.fixed
    (rationalFunction_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place F f a n d)

/-! ## Submodules and generating families -/

def numberFieldSubmoduleDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :=
  HassePredicate.fixed (numberField_submodule_finrank_eq_iff_forall_place K P n)

def rationalFunctionSubmoduleDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_submodule_finrank_eq_iff_forall_place F P n)

def numberFieldSubmoduleQuotientDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :=
  HassePredicate.fixed (numberField_submodule_quotient_finrank_eq_iff_forall_place K P n)

def rationalFunctionSubmoduleQuotientDimensionHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_submodule_quotient_finrank_eq_iff_forall_place F P n)

def numberFieldSubmoduleRangeHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (T : Submodule K N) (f : M →ₗ[K] N) :=
  HassePredicate.fixed (numberField_submodule_eq_range_iff_forall_place K T f)

def rationalFunctionSubmoduleRangeHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N]
    (T : Submodule (RatFunc F) N) (f : M →ₗ[RatFunc F] N) :=
  HassePredicate.fixed (rationalFunction_submodule_eq_range_iff_forall_place F T f)

def numberFieldSpanningFamilyHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] {ι : Type w} (x : ι → M) :=
  HassePredicate.fixed (numberField_span_range_eq_top_iff_forall_place K x)

def rationalFunctionSpanningFamilyHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] {ι : Type w} (x : ι → M) :=
  HassePredicate.fixed (rationalFunction_span_range_eq_top_iff_forall_place F x)

def numberFieldCSASubmoduleMembershipHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (P : Submodule K A.toAlgCat) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mem_baseChange_iff_forall_place K A P a)

def rationalFunctionCSASubmoduleMembershipHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (P : Submodule (RatFunc F) A.toAlgCat) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mem_baseChange_iff_forall_place F A P a)

def numberFieldLinearIndependentHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] {ι : Type w} (x : ι → M) :=
  HassePredicate.fixed (numberField_linearIndependent_iff_forall_place K x)

def rationalFunctionLinearIndependentHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] {ι : Type w} (x : ι → M) :=
  HassePredicate.fixed (rationalFunction_linearIndependent_iff_forall_place F x)

def numberFieldBasisFamilyHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] {ι : Type w} (b : ι → M) :=
  HassePredicate.fixed (numberField_basisFamily_iff_forall_place K b)

def rationalFunctionBasisFamilyHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] {ι : Type w} (b : ι → M) :=
  HassePredicate.fixed (rationalFunction_basisFamily_iff_forall_place F b)

/-! ## Endomorphism invariants -/

def numberFieldLinearMapCharpolyHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (p : Polynomial K) :=
  HassePredicate.fixed (numberField_linearMap_charpoly_eq_iff_forall_place K f p)

def rationalFunctionLinearMapCharpolyHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (p : Polynomial (RatFunc F)) :=
  HassePredicate.fixed (rationalFunction_linearMap_charpoly_eq_iff_forall_place F f p)

def numberFieldLinearMapTraceHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :=
  HassePredicate.fixed (numberField_linearMap_trace_eq_iff_forall_place K f a)

def rationalFunctionLinearMapTraceHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [Module.Finite (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :=
  HassePredicate.fixed (rationalFunction_linearMap_trace_eq_iff_forall_place F f a)

end GaloisForLFunctions.HTGeometry.ABHN
