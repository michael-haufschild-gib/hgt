import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutator
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedIntertwinerDimensions

/-!
# Rigid central-simple-algebra equation Hasse predicates

Solvability of fixed division, commutator, and intertwining equations is reflected by every
completion and by any one completion.  The same holds for fixed regular eigenvalue and generalized
eigenspace-dimension data.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-! ## Algebra equations -/

def numberFieldCSALeftDivisionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place K A a b)
    (numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place K A a b)

def rationalFunctionCSALeftDivisionRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place F A a b)
    (rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place F A a b)

def numberFieldCSARightDivisionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place K A a b)
    (numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place K A a b)

def rationalFunctionCSARightDivisionRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place F A a b)
    (rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place F A a b)

def numberFieldCSACommutatorEquationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place K A a b)
    (numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place K A a b)

def rationalFunctionCSACommutatorEquationRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place F A a b)
    (rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_exists_place F A a b)

def numberFieldCSAIntertwiningDefectEquationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a b c : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place K A a b c)
    (numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place K A a b c)

def rationalFunctionCSAIntertwiningDefectEquationRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, w} (RatFunc F)) (a b c : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place F A a b c)
    (rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place F A a b c)

def numberFieldCSANonzeroIntertwinerRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place K A a b)
    (numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place K A a b)

def rationalFunctionCSANonzeroIntertwinerRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place F A a b)
    (rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place F A a b)

/-! ## Regular and Sylvester generalized eigenspaces -/

def numberFieldCSALeftEigenvalueRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (x : A.carrier) (c : K) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place K A x c)
    (numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place K A x c)

def rationalFunctionCSALeftEigenvalueRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (x : A.carrier) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place F A x c)
    (rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place F A x c)

def numberFieldCSALeftGeneralizedEigenspaceDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (x : A.carrier) (c : K) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place K A x c n d)
    (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place K A x c n d)

def rationalFunctionCSALeftGeneralizedEigenspaceDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (x : A.carrier) (c : RatFunc F) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place F A x c n d)
    (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place F A x c n d)

def numberFieldCSAIntertwinerGeneralizedEigenspaceDimensionRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K)
    (a b : A.carrier) (c : K) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place K A a b c n d)
    (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place K A a b c n d)

def rationalFunctionCSAIntertwinerGeneralizedEigenspaceDimensionRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (c : RatFunc F) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place F A a b c n d)
    (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place F A a b c n d)

end GaloisForLFunctions.HTGeometry.ABHN
