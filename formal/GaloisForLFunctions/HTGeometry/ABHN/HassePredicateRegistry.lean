import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSingularity
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixDiagonal
import GaloisForLFunctions.HTGeometry.ABHN.HasseClassicalMatrixGroups
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialEvaluation
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.HasseCentralSimple
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraNilpotence
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealMembership

/-!
# ABHN Hasse-predicate registry

Closed local--global theorems for number fields and rational function fields are packaged in the
common predicate interface.  This makes local obstruction, pullback, reindexing, and conjunction
available uniformly across algebraic objects and properties.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Prescribed square-matrix rank over a number field, detected at all completions. -/
def numberFieldMatrixRankHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (r : ℕ) :=
  HassePredicate.fixed (numberFieldMatrix_rank_eq_iff_forall_place K n M r)

/-- Prescribed square-matrix rank over `F(t)`, detected at all completions. -/
def rationalFunctionMatrixRankHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (r : ℕ) :=
  HassePredicate.fixed (rationalFunctionMatrix_rank_eq_iff_forall_place F n M r)

/-- Invertibility of a number-field matrix as a Hasse predicate. -/
def numberFieldMatrixUnitHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  HassePredicate.fixed (numberFieldMatrix_isUnit_iff_forall_place K n M)

/-- Invertibility of an `F(t)`-matrix as a Hasse predicate. -/
def rationalFunctionMatrixUnitHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionMatrix_isUnit_iff_forall_place F n M)

/-- Singularity of a number-field matrix as a Hasse predicate. -/
def numberFieldMatrixSingularHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  HassePredicate.fixed (numberFieldMatrix_det_eq_zero_iff_forall_place K n M)

/-- Singularity of an `F(t)`-matrix as a Hasse predicate. -/
def rationalFunctionMatrixSingularHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionMatrix_det_eq_zero_iff_forall_place F n M)

/-- Idempotence of a number-field matrix as a Hasse predicate. -/
def numberFieldMatrixIdempotentHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  HassePredicate.fixed (numberFieldMatrix_isIdempotentElem_iff_forall_place K n M)

/-- Idempotence of an `F(t)`-matrix as a Hasse predicate. -/
def rationalFunctionMatrixIdempotentHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionMatrix_isIdempotentElem_iff_forall_place F n M)

/-- Diagonality of a number-field matrix as a Hasse predicate. -/
def numberFieldMatrixDiagonalHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) (M : Matrix n n K) :=
  HassePredicate.fixed (numberFieldMatrix_isDiag_iff_forall_place K n M)

/-- Diagonality of an `F(t)`-matrix as a Hasse predicate. -/
def rationalFunctionMatrixDiagonalHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) (M : Matrix n n (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionMatrix_isDiag_iff_forall_place F n M)

/-- Orthogonal-group membership of a number-field matrix as a Hasse predicate. -/
def numberFieldOrthogonalMatrixHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  HassePredicate.fixed (numberFieldMatrix_mem_orthogonalGroup_iff_forall_place K n M)

/-- Orthogonal-group membership of an `F(t)`-matrix as a Hasse predicate. -/
def rationalFunctionOrthogonalMatrixHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionMatrix_mem_orthogonalGroup_iff_forall_place F n M)

/-- Vanishing of a number-field polynomial at a point as a Hasse predicate. -/
def numberFieldPolynomialEvaluationHassePredicate
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) (x : K) :=
  HassePredicate.fixed (numberFieldPolynomial_eval_eq_zero_iff_forall_place K p x)

/-- Vanishing of an `F(t)`-polynomial at a point as a Hasse predicate. -/
def rationalFunctionPolynomialEvaluationHassePredicate
    (F : Type u) [Field F] [Finite F]
    (p : Polynomial (RatFunc F)) (x : RatFunc F) :=
  HassePredicate.fixed (rationalFunctionPolynomial_eval_eq_zero_iff_forall_place F p x)

/-- Separability of a number-field polynomial as a Hasse predicate. -/
def numberFieldPolynomialSeparableHassePredicate
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :=
  HassePredicate.fixed (numberFieldPolynomial_separable_iff_forall_place K p)

/-- Separability of an `F(t)`-polynomial as a Hasse predicate. -/
def rationalFunctionPolynomialSeparableHassePredicate
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionPolynomial_separable_iff_forall_place F p)

/-- Dimension of a number-field module as a Hasse predicate. -/
def numberFieldModuleFinrankHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (n : ℕ) :=
  HassePredicate.fixed (numberField_module_finrank_eq_iff_forall_place K (M := M) n)

/-- Dimension of an `F(t)`-module as a Hasse predicate. -/
def rationalFunctionModuleFinrankHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] (n : ℕ) :=
  HassePredicate.fixed (rationalFunction_module_finrank_eq_iff_forall_place F (M := M) n)

/-- Injectivity of a number-field linear map as a Hasse predicate. -/
def numberFieldLinearMapInjectiveHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :=
  HassePredicate.fixed (numberFieldLinearMap_injective_iff_forall_place K f)

/-- Injectivity of an `F(t)`-linear map as a Hasse predicate. -/
def rationalFunctionLinearMapInjectiveHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) (N : Type w) [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) :=
  HassePredicate.fixed (rationalFunctionLinearMap_injective_iff_forall_place F f)

/-- Central simplicity over a number field as a Hasse predicate. -/
def numberFieldCentralSimpleHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [Module.Finite K A] :=
  HassePredicate.fixed (numberField_isSimpleRing_iff_forall_place K (A := A))

/-- Central simplicity over `F(t)` as a Hasse predicate. -/
def rationalFunctionCentralSimpleHassePredicate
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A]
    [Algebra.IsCentral (RatFunc F) A] [Module.Finite (RatFunc F) A] :=
  HassePredicate.fixed (rationalFunction_isSimpleRing_iff_forall_place F (A := A))

/-- Nilpotence of an element of a number-field CSA as a Hasse predicate. -/
def numberFieldCSANilpotentHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_isNilpotent_iff_forall_place K A a)

/-- Nilpotence of an element of an `F(t)`-CSA as a Hasse predicate. -/
def rationalFunctionCSANilpotentHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_forall_place F A a)

/-- Ideal membership in a number-field algebra as a Hasse predicate. -/
def numberFieldIdealMembershipHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [CommRing A] [Algebra K A] (I : Ideal A) (a : A) :=
  HassePredicate.fixed (numberField_ideal_mem_map_iff_forall_place K I a)

/-- Ideal membership in an `F(t)`-algebra as a Hasse predicate. -/
def rationalFunctionIdealMembershipHassePredicate
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (a : A) :=
  HassePredicate.fixed (rationalFunction_ideal_mem_map_iff_forall_place F I a)

end GaloisForLFunctions.HTGeometry.ABHN
