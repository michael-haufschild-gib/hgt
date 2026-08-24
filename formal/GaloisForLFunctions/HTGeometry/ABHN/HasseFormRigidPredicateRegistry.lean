import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseQuadraticForms
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormNondegenerate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraTraceForm

/-!
# Rigid form-theoretic Hasse predicates

Equality, fixed isotropy data, and nondegeneracy of quadratic, bilinear, and algebra trace forms are
reflected by every completion and by any one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-! ## Quadratic forms -/

def numberFieldQuadraticFormEqualityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q₁ Q₂ : QuadraticForm K M) :=
  RigidHassePredicate.fixed
    (numberField_quadraticForm_eq_iff_forall_place K Q₁ Q₂)
    (numberField_quadraticForm_eq_iff_exists_place K Q₁ Q₂)

def rationalFunctionQuadraticFormEqualityRigidHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q₁ Q₂ : QuadraticForm (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_quadraticForm_eq_iff_forall_place F Q₁ Q₂)
    (rationalFunction_quadraticForm_eq_iff_exists_place F Q₁ Q₂)

def numberFieldQuadraticFormNondegenerateRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) :=
  RigidHassePredicate.fixed
    (numberField_quadraticForm_nondegenerate_iff_forall_place K Q)
    (numberField_quadraticForm_nondegenerate_iff_exists_place K Q)

def rationalFunctionQuadraticFormNondegenerateRigidHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [FiniteDimensional (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_quadraticForm_nondegenerate_iff_forall_place F Q)
    (rationalFunction_quadraticForm_nondegenerate_iff_exists_place F Q)

def numberFieldQuadraticFormValueZeroRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  RigidHassePredicate.fixed
    (numberField_quadraticForm_apply_eq_zero_iff_forall_place K Q x)
    (numberField_quadraticForm_apply_eq_zero_iff_exists_place K Q x)

def rationalFunctionQuadraticFormValueZeroRigidHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  RigidHassePredicate.fixed
    (rationalFunction_quadraticForm_apply_eq_zero_iff_forall_place F Q x)
    (rationalFunction_quadraticForm_apply_eq_zero_iff_exists_place F Q x)

def numberFieldQuadraticFormIsotropicVectorRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :=
  RigidHassePredicate.fixed
    (numberField_quadraticForm_isotropicVector_iff_forall_place K Q x)
    (numberField_quadraticForm_isotropicVector_iff_exists_place K Q x)

def rationalFunctionQuadraticFormIsotropicVectorRigidHassePredicate
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :=
  RigidHassePredicate.fixed
    (rationalFunction_quadraticForm_isotropicVector_iff_forall_place F Q x)
    (rationalFunction_quadraticForm_isotropicVector_iff_exists_place F Q x)

/-! ## Bilinear and trace forms -/

def numberFieldBilinearFormEqualityRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] (B C : LinearMap.BilinForm K M) :=
  RigidHassePredicate.fixed
    (numberField_bilinForm_eq_iff_forall_place K B C)
    (numberField_bilinForm_eq_iff_exists_place K B C)

def rationalFunctionBilinearFormEqualityRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M]
    (B C : LinearMap.BilinForm (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_bilinForm_eq_iff_forall_place F B C)
    (rationalFunction_bilinForm_eq_iff_exists_place F B C)

def numberFieldBilinearFormNondegenerateRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (M : Type v) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (B : LinearMap.BilinForm K M) :=
  RigidHassePredicate.fixed
    (numberField_bilinForm_nondegenerate_iff_forall_place K B)
    (numberField_bilinForm_nondegenerate_iff_exists_place K B)

def rationalFunctionBilinearFormNondegenerateRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (M : Type v) [AddCommGroup M] [Module (RatFunc F) M] [FiniteDimensional (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :=
  RigidHassePredicate.fixed
    (rationalFunction_bilinForm_nondegenerate_iff_forall_place F B)
    (rationalFunction_bilinForm_nondegenerate_iff_exists_place F B)

def numberFieldAlgebraTraceFormNondegenerateRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (B : Type w)
    [CommRing B] [Algebra K B] [Module.Free K B] [Module.Finite K B]
    (ι : Type v) [Fintype ι] [DecidableEq ι] (e : Module.Basis ι K B) :=
  RigidHassePredicate.fixed
    (numberField_algebra_traceForm_nondegenerate_iff_forall_place K e)
    (numberField_algebra_traceForm_nondegenerate_iff_exists_place K e)

def rationalFunctionAlgebraTraceFormNondegenerateRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (B : Type w)
    [CommRing B] [Algebra (RatFunc F) B] [Module.Free (RatFunc F) B]
    [Module.Finite (RatFunc F) B] (ι : Type v) [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι (RatFunc F) B) :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_traceForm_nondegenerate_iff_forall_place F e)
    (rationalFunction_algebra_traceForm_nondegenerate_iff_exists_place F e)

end GaloisForLFunctions.HTGeometry.ABHN
