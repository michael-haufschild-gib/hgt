import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness
import GaloisForLFunctions.HTGeometry.ABHN.HasseGeometricProperties

/-!
# Rigid geometric Hasse predicates

Finiteness and standard geometric properties of global-field modules and commutative algebras are
reflected by every completion and by any one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-! ## Finiteness -/

def numberFieldModuleFiniteRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (M : Type w)
    [AddCommGroup M] [Module K M] :=
  RigidHassePredicate.fixed
    (numberField_module_finite_iff_forall_place K (M := M))
    (numberField_module_finite_iff_exists_place K (M := M))

def rationalFunctionModuleFiniteRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (M : Type w)
    [AddCommGroup M] [Module (RatFunc F) M] :=
  RigidHassePredicate.fixed
    (rationalFunction_module_finite_iff_forall_place F (M := M))
    (rationalFunction_module_finite_iff_exists_place F (M := M))

def numberFieldAlgebraFiniteTypeRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_finiteType_iff_forall_place K (A := A))
    (numberField_algebra_finiteType_iff_exists_place K (A := A))

def rationalFunctionAlgebraFiniteTypeRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_finiteType_iff_forall_place F (A := A))
    (rationalFunction_algebra_finiteType_iff_exists_place F (A := A))

def numberFieldAlgebraFinitePresentationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_finitePresentation_iff_forall_place K (A := A))
    (numberField_algebra_finitePresentation_iff_exists_place K (A := A))

def rationalFunctionAlgebraFinitePresentationRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_finitePresentation_iff_forall_place F (A := A))
    (rationalFunction_algebra_finitePresentation_iff_exists_place F (A := A))

/-! ## Smooth, unramified, and étale algebras -/

def numberFieldAlgebraSmoothRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_smooth_iff_forall_place K (A := A))
    (numberField_algebra_smooth_iff_exists_place K (A := A))

def rationalFunctionAlgebraSmoothRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_smooth_iff_forall_place F (A := A))
    (rationalFunction_algebra_smooth_iff_exists_place F (A := A))

def numberFieldAlgebraUnramifiedRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_unramified_iff_forall_place K (A := A))
    (numberField_algebra_unramified_iff_exists_place K (A := A))

def rationalFunctionAlgebraUnramifiedRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_unramified_iff_forall_place F (A := A))
    (rationalFunction_algebra_unramified_iff_exists_place F (A := A))

def numberFieldAlgebraEtaleRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_etale_iff_forall_place K (A := A))
    (numberField_algebra_etale_iff_exists_place K (A := A))

def rationalFunctionAlgebraEtaleRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_etale_iff_forall_place F (A := A))
    (rationalFunction_algebra_etale_iff_exists_place F (A := A))

def numberFieldAlgebraFiniteEtaleRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : Type w)
    [CommRing A] [Algebra K A] :=
  RigidHassePredicate.fixed
    (numberField_algebra_finiteEtale_iff_forall_place K (A := A))
    (numberField_algebra_finiteEtale_iff_exists_place K (A := A))

def rationalFunctionAlgebraFiniteEtaleRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : Type w)
    [CommRing A] [Algebra (RatFunc F) A] :=
  RigidHassePredicate.fixed
    (rationalFunction_algebra_finiteEtale_iff_forall_place F (A := A))
    (rationalFunction_algebra_finiteEtale_iff_exists_place F (A := A))

end GaloisForLFunctions.HTGeometry.ABHN
