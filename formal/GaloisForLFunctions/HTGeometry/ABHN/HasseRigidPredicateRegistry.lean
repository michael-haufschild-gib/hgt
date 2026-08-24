import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixDiagonal
import GaloisForLFunctions.HTGeometry.ABHN.HasseClassicalMatrixGroups
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapCokernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleQuotients
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence
import GaloisForLFunctions.HTGeometry.ABHN.HasseBasisFamily
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleStrictness

/-!
# Rigid Hasse-predicate registry

Properties whose global truth is equivalent both to truth at every completion and to truth at one
completion.  These are faithfully-flat rigidity laws: all places carry the same truth value, unlike
reciprocity systems where the collection of places is essential.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-! ## Matrix rigidity -/

def numberFieldMatrixRankRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (r : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_rank_eq_iff_forall_place K n M r)
    (numberFieldMatrix_rank_eq_iff_exists_place K n M r)

def rationalFunctionMatrixRankRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (r : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_rank_eq_iff_forall_place F n M r)
    (rationalFunctionMatrix_rank_eq_iff_exists_place F n M r)

def numberFieldMatrixUnitRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_isUnit_iff_forall_place K n M)
    (numberFieldMatrix_isUnit_iff_exists_place K n M)

def rationalFunctionMatrixUnitRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_isUnit_iff_forall_place F n M)
    (rationalFunctionMatrix_isUnit_iff_exists_place F n M)

def numberFieldMatrixSingularRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_det_eq_zero_iff_forall_place K n M)
    (numberFieldMatrix_det_eq_zero_iff_exists_place K n M)

def rationalFunctionMatrixSingularRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_det_eq_zero_iff_forall_place F n M)
    (rationalFunctionMatrix_det_eq_zero_iff_exists_place F n M)

def numberFieldMatrixIdempotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_isIdempotentElem_iff_forall_place K n M)
    (numberFieldMatrix_isIdempotentElem_iff_exists_place K n M)

def rationalFunctionMatrixIdempotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_isIdempotentElem_iff_forall_place F n M)
    (rationalFunctionMatrix_isIdempotentElem_iff_exists_place F n M)

def numberFieldOrthogonalMatrixRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_mem_orthogonalGroup_iff_forall_place K n M)
    (numberFieldMatrix_mem_orthogonalGroup_iff_exists_place K n M)

def rationalFunctionOrthogonalMatrixRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_mem_orthogonalGroup_iff_forall_place F n M)
    (rationalFunctionMatrix_mem_orthogonalGroup_iff_exists_place F n M)

def numberFieldOrthogonalRowsRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    {m : Type v} {n : Type w} [Fintype n] (M : Matrix m n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_hasOrthogonalRows_iff_forall_place K M)
    (numberFieldMatrix_hasOrthogonalRows_iff_exists_place K M)

def rationalFunctionOrthogonalRowsRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    {m : Type v} {n : Type w} [Fintype n] (M : Matrix m n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_hasOrthogonalRows_iff_forall_place F M)
    (rationalFunctionMatrix_hasOrthogonalRows_iff_exists_place F M)

def numberFieldOrthogonalColsRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    {m : Type v} {n : Type w} [Fintype m] (M : Matrix m n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_hasOrthogonalCols_iff_forall_place K M)
    (numberFieldMatrix_hasOrthogonalCols_iff_exists_place K M)

def rationalFunctionOrthogonalColsRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    {m : Type v} {n : Type w} [Fintype m] (M : Matrix m n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_hasOrthogonalCols_iff_forall_place F M)
    (rationalFunctionMatrix_hasOrthogonalCols_iff_exists_place F M)

def numberFieldSpecialOrthogonalMatrixRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_mem_specialOrthogonalGroup_iff_forall_place K n M)
    (numberFieldMatrix_mem_specialOrthogonalGroup_iff_exists_place K n M)

def rationalFunctionSpecialOrthogonalMatrixRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_mem_specialOrthogonalGroup_iff_forall_place F n M)
    (rationalFunctionMatrix_mem_specialOrthogonalGroup_iff_exists_place F n M)

/-! ## Linear and submodule rigidity -/

def numberFieldLinearMapKernelDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_ker_finrank_eq_iff_forall_place K f n)
    (numberField_linearMap_ker_finrank_eq_iff_exists_place K f n)

def rationalFunctionLinearMapKernelDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_ker_finrank_eq_iff_forall_place F f n)
    (rationalFunction_linearMap_ker_finrank_eq_iff_exists_place F f n)

def numberFieldLinearMapRangeDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_range_finrank_eq_iff_forall_place K f n)
    (numberField_linearMap_range_finrank_eq_iff_exists_place K f n)

def rationalFunctionLinearMapRangeDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_range_finrank_eq_iff_forall_place F f n)
    (rationalFunction_linearMap_range_finrank_eq_iff_exists_place F f n)

def numberFieldLinearMapCokernelDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_cokernel_finrank_eq_iff_forall_place K f n)
    (numberField_linearMap_cokernel_finrank_eq_iff_exists_place K f n)

def rationalFunctionLinearMapCokernelDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_cokernel_finrank_eq_iff_forall_place F f n)
    (rationalFunction_linearMap_cokernel_finrank_eq_iff_exists_place F f n)

def numberFieldLinearMapGeneralizedEigenspaceDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (a : K) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place K f a n d)
    (numberField_linearMap_generalizedEigenKernel_finrank_eq_iff_exists_place K f a n d)

def rationalFunctionLinearMapGeneralizedEigenspaceDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (a : RatFunc F) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearMap_generalizedEigenKernel_finrank_eq_iff_forall_place F f a n d)
    (rationalFunction_linearMap_generalizedEigenKernel_finrank_eq_iff_exists_place F f a n d)

def numberFieldSubmoduleDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_submodule_finrank_eq_iff_forall_place K P n)
    (numberField_submodule_finrank_eq_iff_exists_place K P n)

def rationalFunctionSubmoduleDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_submodule_finrank_eq_iff_forall_place F P n)
    (rationalFunction_submodule_finrank_eq_iff_exists_place F P n)

def numberFieldSubmoduleQuotientDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_submodule_quotient_finrank_eq_iff_forall_place K P n)
    (numberField_submodule_quotient_finrank_eq_iff_exists_place K P n)

def rationalFunctionSubmoduleQuotientDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_submodule_quotient_finrank_eq_iff_forall_place F P n)
    (rationalFunction_submodule_quotient_finrank_eq_iff_exists_place F P n)

def numberFieldLinearIndependentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] {ι : Type w} (x : ι → M) :=
  RigidHassePredicate.fixed
    (numberField_linearIndependent_iff_forall_place K x)
    (numberField_linearIndependent_iff_exists_place K x)

def rationalFunctionLinearIndependentRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] {ι : Type w} (x : ι → M) :=
  RigidHassePredicate.fixed
    (rationalFunction_linearIndependent_iff_forall_place F x)
    (rationalFunction_linearIndependent_iff_exists_place F x)

def numberFieldBasisFamilyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] {ι : Type w} (b : ι → M) :=
  RigidHassePredicate.fixed
    (numberField_basisFamily_iff_forall_place K b)
    (numberField_basisFamily_iff_exists_place K b)

def rationalFunctionBasisFamilyRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] {ι : Type w} (b : ι → M) :=
  RigidHassePredicate.fixed
    (rationalFunction_basisFamily_iff_forall_place F b)
    (rationalFunction_basisFamily_iff_exists_place F b)

def numberFieldSubmoduleContainmentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P Q : Submodule K M) :=
  RigidHassePredicate.fixed
    (numberField_submodule_le_iff_forall_place K P Q)
    (numberField_submodule_le_iff_exists_place K P Q)

def rationalFunctionSubmoduleContainmentRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_submodule_le_iff_forall_place F P Q)
    (rationalFunction_submodule_le_iff_exists_place F P Q)

def numberFieldSubmoduleEqualityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P Q : Submodule K M) :=
  RigidHassePredicate.fixed
    (numberField_submodule_eq_iff_forall_place K P Q)
    (numberField_submodule_eq_iff_exists_place K P Q)

def rationalFunctionSubmoduleEqualityRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_submodule_eq_iff_forall_place F P Q)
    (rationalFunction_submodule_eq_iff_exists_place F P Q)

def numberFieldSubmoduleStrictContainmentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (P Q : Submodule K M) :=
  RigidHassePredicate.fixed
    (numberField_submodule_lt_iff_forall_place K P Q)
    (numberField_submodule_lt_iff_exists_place K P Q)

def rationalFunctionSubmoduleStrictContainmentRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_submodule_lt_iff_forall_place F P Q)
    (rationalFunction_submodule_lt_iff_exists_place F P Q)

end GaloisForLFunctions.HTGeometry.ABHN
