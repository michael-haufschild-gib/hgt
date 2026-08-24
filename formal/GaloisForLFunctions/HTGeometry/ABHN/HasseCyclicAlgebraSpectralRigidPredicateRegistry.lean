import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwinerInvariants
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseRegularInvariants
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseSpectral
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseGeneralizedEigenDimensions
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseIntertwinerCokernels
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseGeneralizedIntertwinerDimensions

/-!
# Rigid spectral Hasse predicates for cyclic algebras

Sylvester equations, intertwiner kernel and cokernel dimensions, generalized eigenspaces, and
regular-representation invariants of nonzero cyclic Galois algebras are completion-rigid.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-! ## Number fields -/

section NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
  (a : K) (ha : a ≠ 0)

def numberFieldCyclicAlgebraIntertwiningEquationRigidHassePredicate
    (x y z : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_forall_place
      K L a ha x y z)
    (numberField_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
      K L a ha x y z)

def numberFieldCyclicAlgebraNonzeroIntertwinerRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_forall_place
      K L a ha x y)
    (numberField_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
      K L a ha x y)

def numberFieldCyclicAlgebraIntertwinerFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_forall_place
      K L a ha x y d)
    (numberField_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
      K L a ha x y d)

def numberFieldCyclicAlgebraIntertwinerCharpolyRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (q : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_forall_place
      K L a ha x y q)
    (numberField_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
      K L a ha x y q)

def numberFieldCyclicAlgebraIntertwinerTraceRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (t : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_forall_place
      K L a ha x y t)
    (numberField_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
      K L a ha x y t)

def numberFieldCyclicAlgebraIntertwinerDetRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (d : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerDet_eq_iff_forall_place
      K L a ha x y d)
    (numberField_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
      K L a ha x y d)

def numberFieldCyclicAlgebraRegularCharpolyRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) (q : Polynomial K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_regularCharpoly_eq_iff_forall_place K L a ha x q)
    (numberField_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place K L a ha x q)

def numberFieldCyclicAlgebraRegularTraceRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) (t : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_regularTrace_eq_iff_forall_place K L a t ha x)
    (numberField_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place K L a t ha x)

def numberFieldCyclicAlgebraRegularNormRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) (n : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_regularNorm_eq_iff_forall_place K L a n ha x)
    (numberField_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place K L a n ha x)

def numberFieldCyclicAlgebraRegularCharpolySeparableRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_regularCharpoly_separable_iff_forall_place
      K L a ha x)
    (numberField_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place
      K L a ha x)

def numberFieldCyclicAlgebraLeftEigenvalueRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) (c : K) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_forall_place
      K L a ha x c)
    (numberField_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
      K L a ha x c)

def numberFieldCyclicAlgebraGeneralizedLeftEigenspaceFinrankRigidHassePredicate
    (x : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
      K L a ha x c n d)
    (numberField_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      K L a ha x c n d)

def numberFieldCyclicAlgebraIntertwinerCokernelFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_forall_place
      K L a ha x y d)
    (numberField_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
      K L a ha x y d)

def numberFieldCyclicAlgebraGeneralizedIntertwinerFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra K L a) (c : K) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_forall_place
      K L a ha x y c n d)
    (numberField_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
      K L a ha x y c n d)

end NumberField

/-! ## Rational function fields -/

section RationalFunction

variable (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
  [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
  (a : RatFunc F) (ha : a ≠ 0)

def rationalFunctionCyclicAlgebraIntertwiningEquationRigidHassePredicate
    (x y z : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_forall_place
      F L a ha x y z)
    (rationalFunction_cyclicGaloisAlgebra_exists_intertwining_defect_eq_iff_exists_place
      F L a ha x y z)

def rationalFunctionCyclicAlgebraNonzeroIntertwinerRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_forall_place
      F L a ha x y)
    (rationalFunction_cyclicGaloisAlgebra_exists_nonzero_intertwiner_iff_exists_place
      F L a ha x y)

def rationalFunctionCyclicAlgebraIntertwinerFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_forall_place
      F L a ha x y d)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerFinrank_eq_iff_exists_place
      F L a ha x y d)

def rationalFunctionCyclicAlgebraIntertwinerCharpolyRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (q : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_forall_place
      F L a ha x y q)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCharpoly_eq_iff_exists_place
      F L a ha x y q)

def rationalFunctionCyclicAlgebraIntertwinerTraceRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (t : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_forall_place
      F L a ha x y t)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerTrace_eq_iff_exists_place
      F L a ha x y t)

def rationalFunctionCyclicAlgebraIntertwinerDetRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerDet_eq_iff_forall_place
      F L a ha x y d)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerDet_eq_iff_exists_place
      F L a ha x y d)

def rationalFunctionCyclicAlgebraRegularCharpolyRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) (q : Polynomial (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_eq_iff_forall_place F L a ha x q)
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_eq_iff_exists_place F L a ha x q)

def rationalFunctionCyclicAlgebraRegularTraceRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) (t : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_regularTrace_eq_iff_forall_place F L a t ha x)
    (rationalFunction_cyclicGaloisAlgebra_regularTrace_eq_iff_exists_place F L a t ha x)

def rationalFunctionCyclicAlgebraRegularNormRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) (n : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_regularNorm_eq_iff_forall_place F L a n ha x)
    (rationalFunction_cyclicGaloisAlgebra_regularNorm_eq_iff_exists_place F L a n ha x)

def rationalFunctionCyclicAlgebraRegularCharpolySeparableRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_separable_iff_forall_place
      F L a ha x)
    (rationalFunction_cyclicGaloisAlgebra_regularCharpoly_separable_iff_exists_place
      F L a ha x)

def rationalFunctionCyclicAlgebraLeftEigenvalueRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_forall_place
      F L a ha x c)
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_eigenKernel_ne_bot_iff_exists_place
      F L a ha x c)

def rationalFunctionCyclicAlgebraGeneralizedLeftEigenspaceFinrankRigidHassePredicate
    (x : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
      F L a ha x c n d)
    (rationalFunction_cyclicGaloisAlgebra_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
      F L a ha x c n d)

def rationalFunctionCyclicAlgebraIntertwinerCokernelFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_forall_place
      F L a ha x y d)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerCokernelFinrank_eq_iff_exists_place
      F L a ha x y d)

def rationalFunctionCyclicAlgebraGeneralizedIntertwinerFinrankRigidHassePredicate
    (x y : cyclicGaloisAlgebra (RatFunc F) L a) (c : RatFunc F) (n d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_forall_place
      F L a ha x y c n d)
    (rationalFunction_cyclicGaloisAlgebra_intertwinerGeneralizedEigenKernel_finrank_eq_iff_exists_place
      F L a ha x y c n d)

end RationalFunction

end GaloisForLFunctions.HTGeometry.ABHN
