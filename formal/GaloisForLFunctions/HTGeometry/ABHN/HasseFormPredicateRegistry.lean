import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseQuadraticForms
import GaloisForLFunctions.HTGeometry.ABHN.FormFailureHasse

/-!
# Quadratic-form Hasse-predicate registry

Completionwise detection of equality, nondegeneracy, fixed-value vanishing, fixed isotropic
vectors, and their rigid failure predicates over number fields and rational function fields.
These are fixed-vector/form local--global laws, not the full Hasse--Minkowski existence theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-! ## Positive predicates -/

def numberFieldQuadraticFormEqualityHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q₁ Q₂ : QuadraticForm K M) :=
  HassePredicate.fixed (numberField_quadraticForm_eq_iff_forall_place K Q₁ Q₂)

def rationalFunctionQuadraticFormEqualityHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q₁ Q₂ : QuadraticForm (RatFunc F) M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_eq_iff_forall_place F Q₁ Q₂)

def numberFieldQuadraticFormNondegenerateHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) :=
  HassePredicate.fixed (numberField_quadraticForm_nondegenerate_iff_forall_place K Q)

def rationalFunctionQuadraticFormNondegenerateHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [FiniteDimensional (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_nondegenerate_iff_forall_place F Q)

def numberFieldQuadraticFormValueZeroHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  HassePredicate.fixed (numberField_quadraticForm_apply_eq_zero_iff_forall_place K Q x)

def rationalFunctionQuadraticFormValueZeroHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_apply_eq_zero_iff_forall_place F Q x)

def numberFieldQuadraticFormIsotropicVectorHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  HassePredicate.fixed (numberField_quadraticForm_isotropicVector_iff_forall_place K Q x)

def rationalFunctionQuadraticFormIsotropicVectorHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_isotropicVector_iff_forall_place F Q x)

/-! ## Rigid failure predicates -/

def numberFieldQuadraticFormInequalityHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q₁ Q₂ : QuadraticForm K M) :=
  HassePredicate.fixed (numberField_quadraticForm_ne_iff_forall_place K Q₁ Q₂)

def rationalFunctionQuadraticFormInequalityHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q₁ Q₂ : QuadraticForm (RatFunc F) M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_ne_iff_forall_place F Q₁ Q₂)

def numberFieldQuadraticFormDegenerateHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) :=
  HassePredicate.fixed (numberField_quadraticForm_degenerate_iff_forall_place K Q)

def rationalFunctionQuadraticFormDegenerateHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [FiniteDimensional (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_degenerate_iff_forall_place F Q)

def numberFieldQuadraticFormValueNonzeroHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  HassePredicate.fixed (numberField_quadraticForm_apply_ne_zero_iff_forall_place K Q x)

def rationalFunctionQuadraticFormValueNonzeroHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  HassePredicate.fixed (rationalFunction_quadraticForm_apply_ne_zero_iff_forall_place F Q x)

def numberFieldQuadraticFormNotIsotropicVectorHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  HassePredicate.fixed (numberField_quadraticForm_not_isotropicVector_iff_forall_place K Q x)

def rationalFunctionQuadraticFormNotIsotropicVectorHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  HassePredicate.fixed
    (rationalFunction_quadraticForm_not_isotropicVector_iff_forall_place F Q x)

end GaloisForLFunctions.HTGeometry.ABHN
