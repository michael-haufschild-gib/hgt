import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialIdentity
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixCharpolySeparable

/-!
# Rigid polynomial and spectral Hasse predicates

Polynomial identities, fixed global solution systems, separability, and prescribed matrix spectral
data are reflected by every completion and by any one completion.  These are rigid faithfully-flat
laws rather than reciprocity principles involving a joint sum over places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-! ## Polynomial identity and evaluation rigidity -/

def numberFieldPolynomialIdentityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberFieldPolynomial_map_eq_zero_iff_forall_place K p)
    (numberFieldPolynomial_map_eq_zero_iff_exists_place K p)

def rationalFunctionPolynomialIdentityRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionPolynomial_map_eq_zero_iff_forall_place F p)
    (rationalFunctionPolynomial_map_eq_zero_iff_exists_place F p)

def numberFieldMvPolynomialIdentityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] {σ : Type v} (p : MvPolynomial σ K) :=
  RigidHassePredicate.fixed
    (numberFieldMvPolynomial_map_eq_zero_iff_forall_place K p)
    (numberFieldMvPolynomial_map_eq_zero_iff_exists_place K p)

def rationalFunctionMvPolynomialIdentityRigidHassePredicate
    (F : Type u) [Field F] [Finite F] {σ : Type v}
    (p : MvPolynomial σ (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMvPolynomial_map_eq_zero_iff_forall_place F p)
    (rationalFunctionMvPolynomial_map_eq_zero_iff_exists_place F p)

def numberFieldPolynomialEvaluationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) (x : K) :=
  RigidHassePredicate.fixed
    (numberFieldPolynomial_eval_eq_zero_iff_forall_place K p x)
    (numberFieldPolynomial_eval_eq_zero_iff_exists_place K p x)

def rationalFunctionPolynomialEvaluationRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (p : Polynomial (RatFunc F)) (x : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionPolynomial_eval_eq_zero_iff_forall_place F p x)
    (rationalFunctionPolynomial_eval_eq_zero_iff_exists_place F p x)

def numberFieldMvPolynomialEvaluationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] {σ : Type v}
    (p : MvPolynomial σ K) (x : σ → K) :=
  RigidHassePredicate.fixed
    (numberFieldMvPolynomial_eval_eq_zero_iff_forall_place K p x)
    (numberFieldMvPolynomial_eval_eq_zero_iff_exists_place K p x)

def rationalFunctionMvPolynomialEvaluationRigidHassePredicate
    (F : Type u) [Field F] [Finite F] {σ : Type v}
    (p : MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionMvPolynomial_eval_eq_zero_iff_forall_place F p x)
    (rationalFunctionMvPolynomial_eval_eq_zero_iff_exists_place F p x)

def numberFieldMvPolynomialSystemRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] {σ : Type v} {ι : Type w}
    (P : ι → MvPolynomial σ K) (x : σ → K) :=
  RigidHassePredicate.fixed
    (numberFieldMvPolynomialSystem_eval_eq_zero_iff_forall_place K P x)
    (numberFieldMvPolynomialSystem_eval_eq_zero_iff_exists_place K P x)

def rationalFunctionMvPolynomialSystemRigidHassePredicate
    (F : Type u) [Field F] [Finite F] {σ : Type v} {ι : Type w}
    (P : ι → MvPolynomial σ (RatFunc F)) (x : σ → RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionMvPolynomialSystem_eval_eq_zero_iff_forall_place F P x)
    (rationalFunctionMvPolynomialSystem_eval_eq_zero_iff_exists_place F P x)

def numberFieldPolynomialSeparableRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (p : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberFieldPolynomial_separable_iff_forall_place K p)
    (numberFieldPolynomial_separable_iff_exists_place K p)

def rationalFunctionPolynomialSeparableRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (p : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionPolynomial_separable_iff_forall_place F p)
    (rationalFunctionPolynomial_separable_iff_exists_place F p)

/-! ## Matrix spectral rigidity -/

def numberFieldMatrixCharpolySeparableRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_charpoly_separable_iff_forall_place K n M)
    (numberFieldMatrix_charpoly_separable_iff_exists_place K n M)

def rationalFunctionMatrixCharpolySeparableRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_charpoly_separable_iff_forall_place F n M)
    (rationalFunctionMatrix_charpoly_separable_iff_exists_place F n M)

def numberFieldMatrixCharpolyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (p : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_charpoly_eq_iff_forall_place K n M p)
    (numberFieldMatrix_charpoly_eq_iff_exists_place K n M p)

def rationalFunctionMatrixCharpolyRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (p : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_charpoly_eq_iff_forall_place F n M p)
    (rationalFunctionMatrix_charpoly_eq_iff_exists_place F n M p)

def numberFieldMatrixDeterminantRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (c : K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_det_eq_iff_forall_place K n M c)
    (numberFieldMatrix_det_eq_iff_exists_place K n M c)

def rationalFunctionMatrixDeterminantRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_det_eq_iff_forall_place F n M c)
    (rationalFunctionMatrix_det_eq_iff_exists_place F n M c)

def numberFieldMatrixTraceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] (M : Matrix n n K) (c : K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_trace_eq_iff_forall_place K n M c)
    (numberFieldMatrix_trace_eq_iff_exists_place K n M c)

def rationalFunctionMatrixTraceRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] (M : Matrix n n (RatFunc F)) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_trace_eq_iff_forall_place F n M c)
    (rationalFunctionMatrix_trace_eq_iff_exists_place F n M c)

end GaloisForLFunctions.HTGeometry.ABHN
