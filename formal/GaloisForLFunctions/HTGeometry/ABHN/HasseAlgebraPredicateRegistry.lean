import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAzumaya
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIdempotents
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEquations
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraUnits
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCenter
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutativity
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutator
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraGeneralizedIntertwinerDimensions
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerCokernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwinerInvariants

/-!
# Central-simple-algebra Hasse-predicate registry

Completionwise local--global predicates for Azumaya descent and internal structure of central
simple algebras over number fields and rational function fields.  Registered properties include
equations and solvability, centrality, commutativity, eigen- and intertwiner dimensions, and
Sylvester characteristic invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-! ## Azumaya, element, and algebra structure -/

def numberFieldAzumayaHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] [Module.Finite K A] :=
  HassePredicate.fixed (numberField_isAzumaya_iff_forall_place K (A := A))

def rationalFunctionAzumayaHassePredicate
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] [Module.Finite (RatFunc F) A] :=
  HassePredicate.fixed (rationalFunction_isAzumaya_iff_forall_place F (A := A))

def numberFieldCSAIdempotentHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_isIdempotent_iff_forall_place K A a)

def rationalFunctionCSAIdempotentHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_forall_place F A a)

def numberFieldCSAMultiplicationEquationHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b c : A.toAlgCat) :=
  HassePredicate.fixed (numberFieldLocalScalarExtensionMap_mul_eq_iff_forall_place K A a b c)

def rationalFunctionCSAMultiplicationEquationHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b c : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mul_eq_iff_forall_place F A a b c)

def numberFieldCSAUnitHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a : A.toAlgCat) :=
  HassePredicate.fixed (numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place K A a)

def rationalFunctionCSAUnitHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a : A.toAlgCat) :=
  HassePredicate.fixed (rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place F A a)

def numberFieldCSACentralElementHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a : A.toAlgCat) :=
  HassePredicate.fixed (numberFieldLocalScalarExtensionMap_mem_center_iff_forall_place K A a)

def rationalFunctionCSACentralElementHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a : A.toAlgCat) :=
  HassePredicate.fixed (rationalFunctionLocalScalarExtensionMap_mem_center_iff_forall_place F A a)

def numberFieldCSACommutativeHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) :=
  HassePredicate.fixed (numberFieldLocalScalarExtensionMap_mul_comm_iff_forall_place K A)

def rationalFunctionCSACommutativeHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) :=
  HassePredicate.fixed (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_forall_place F A)

/-! ## Solvability and intertwining -/

def numberFieldCSACommutatorEquationHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place K A a b)

def rationalFunctionCSACommutatorEquationHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place F A a b)

def numberFieldCSALeftDivisionHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place K A a b)

def numberFieldCSARightDivisionHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place K A a b)

def rationalFunctionCSALeftDivisionHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place F A a b)

def rationalFunctionCSARightDivisionHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place F A a b)

def numberFieldCSAIntertwiningDefectHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b c : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place K A a b c)

def numberFieldCSANonzeroIntertwinerHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place K A a b)

def rationalFunctionCSAIntertwiningDefectHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b c : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place
      F A a b c)

def rationalFunctionCSANonzeroIntertwinerHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) (a b : A.toAlgCat) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place F A a b)

/-! ## Spectral and Sylvester invariants -/

def numberFieldCSAEigenvalueHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K) (x : A.toAlgCat) (c : K) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place K A x c)

def rationalFunctionCSAEigenvalueHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (x : A.toAlgCat) (c : RatFunc F) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place F A x c)

def numberFieldCSAGeneralizedEigenspaceDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (x : A.toAlgCat) (c : K) (n d : ℕ) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
      K A x c n d)

def rationalFunctionCSAGeneralizedEigenspaceDimensionHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (x : A.toAlgCat) (c : RatFunc F) (n d : ℕ) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
      F A x c n d)

def numberFieldCSAIntertwinerGeneralizedEigenspaceDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (a b : A.toAlgCat) (c : K) (n d : ℕ) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
      K A a b c n d)

def rationalFunctionCSAIntertwinerGeneralizedEigenspaceDimensionHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (a b : A.toAlgCat) (c : RatFunc F) (n d : ℕ) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
      F A a b c n d)

def numberFieldCSAIntertwinerCokernelDimensionHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (a b : A.toAlgCat) (d : ℕ) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place
      K A a b d)

def rationalFunctionCSAIntertwinerCokernelDimensionHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (a b : A.toAlgCat) (d : ℕ) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwiner_cokernel_finrank_eq_iff_forall_place
      F A a b d)

def numberFieldCSAIntertwinerCharpolyHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (a b : A.toAlgCat) (q : Polynomial K) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place K A a b q)

def numberFieldCSAIntertwinerTraceHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (a b : A.toAlgCat) (c : K) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place K A a b c)

def numberFieldCSAIntertwinerDetHassePredicate
    (K : Type u) [Field K] [NumberField K] (A : CSA K)
    (a b : A.toAlgCat) (c : K) :=
  HassePredicate.fixed
    (numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place K A a b c)

def rationalFunctionCSAIntertwinerCharpolyHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (a b : A.toAlgCat) (q : Polynomial (RatFunc F)) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place F A a b q)

def rationalFunctionCSAIntertwinerTraceHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (a b : A.toAlgCat) (c : RatFunc F) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place F A a b c)

def rationalFunctionCSAIntertwinerDetHassePredicate
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F))
    (a b : A.toAlgCat) (c : RatFunc F) :=
  HassePredicate.fixed
    (rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place F A a b c)

end GaloisForLFunctions.HTGeometry.ABHN
