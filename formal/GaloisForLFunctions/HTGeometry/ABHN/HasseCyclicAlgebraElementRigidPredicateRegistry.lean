import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseAtPlace
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseElements
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraHasseStructure

/-!
# Rigid Hasse predicates for cyclic-algebra elements and equations

Fixed element properties, division and commutator equations, centrality, and centralizer dimension
in a nonzero cyclic Galois algebra are detected at every completion and at any one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-! ## Number fields -/

section NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
  [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]

def numberFieldCyclicAlgebraUnitRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_isUnit_iff_forall_place K L a ha x)
    (numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha) x)

def numberFieldCyclicAlgebraIdempotentRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_isIdempotent_iff_forall_place K L a ha x)
    (numberField_cyclicGaloisAlgebra_isIdempotent_iff_exists_place K L a ha x)

def numberFieldCyclicAlgebraNilpotentRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_isNilpotent_iff_forall_place K L a ha x)
    (numberField_cyclicGaloisAlgebra_isNilpotent_iff_exists_place K L a ha x)

def numberFieldCyclicAlgebraPolynomialRelationRigidHassePredicate
    (a : K) (ha : a ≠ 0) (f : Polynomial K) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_forall_place
      K L a ha f x)
    (numberField_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
      K L a ha f x)

def numberFieldCyclicAlgebraCommutativeRigidHassePredicate (a : K) (ha : a ≠ 0) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_mul_comm_iff_forall_place K L a ha)
    (numberFieldLocalScalarExtensionMap_mul_comm_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha))

def numberFieldCyclicAlgebraLeftAnnihilatorRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_forall_place
      K L a ha x)
    (numberField_exists_nonzero_mulLeft_eq_zero_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha) x)

def numberFieldCyclicAlgebraRightAnnihilatorRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_forall_place
      K L a ha x)
    (numberField_exists_nonzero_mulRight_eq_zero_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha) x)

def numberFieldCyclicAlgebraLeftDivisionRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_forall_place K L a ha x y)
    (numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha) x y)

def numberFieldCyclicAlgebraRightDivisionRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_mulRight_eq_iff_forall_place K L a ha x y)
    (numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place K
      (cyclicGaloisAlgebraCSA K L a ha) x y)

def numberFieldCyclicAlgebraCentralElementRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_mem_center_iff_forall_place K L a ha x)
    (numberField_cyclicGaloisAlgebra_mem_center_iff_exists_place K L a ha x)

def numberFieldCyclicAlgebraCommutatorEquationRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra K L a) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_exists_commutator_eq_iff_forall_place K L a ha x y)
    (numberField_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place K L a ha x y)

def numberFieldCyclicAlgebraCentralizerFinrankRigidHassePredicate
    (a : K) (ha : a ≠ 0) (x : cyclicGaloisAlgebra K L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberField_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_forall_place K L a ha x d)
    (numberField_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place K L a ha x d)

end NumberField

/-! ## Rational function fields -/

section RationalFunction

variable (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
  [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]

def rationalFunctionCyclicAlgebraUnitRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_isUnit_iff_forall_place F L a ha x)
    (rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)

def rationalFunctionCyclicAlgebraIdempotentRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_forall_place F L a ha x)
    (rationalFunction_cyclicGaloisAlgebra_isIdempotent_iff_exists_place F L a ha x)

def rationalFunctionCyclicAlgebraNilpotentRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_forall_place F L a ha x)
    (rationalFunction_cyclicGaloisAlgebra_isNilpotent_iff_exists_place F L a ha x)

def rationalFunctionCyclicAlgebraPolynomialRelationRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (f : Polynomial (RatFunc F))
    (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_forall_place
      F L a ha f x)
    (rationalFunction_cyclicGaloisAlgebra_polynomial_eval₂_eq_zero_iff_exists_place
      F L a ha f x)

def rationalFunctionCyclicAlgebraCommutativeRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_mul_comm_iff_forall_place F L a ha)
    (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha))

def rationalFunctionCyclicAlgebraLeftAnnihilatorRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulLeft_eq_zero_iff_forall_place
      F L a ha x)
    (rationalFunction_exists_nonzero_mulLeft_eq_zero_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)

def rationalFunctionCyclicAlgebraRightAnnihilatorRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_nonzero_mulRight_eq_zero_iff_forall_place
      F L a ha x)
    (rationalFunction_exists_nonzero_mulRight_eq_zero_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x)

def rationalFunctionCyclicAlgebraLeftDivisionRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_mulLeft_eq_iff_forall_place F L a ha x y)
    (rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y)

def rationalFunctionCyclicAlgebraRightDivisionRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_mulRight_eq_iff_forall_place F L a ha x y)
    (rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place F
      (cyclicGaloisAlgebraCSA (RatFunc F) L a ha) x y)

def rationalFunctionCyclicAlgebraCentralElementRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_mem_center_iff_forall_place F L a ha x)
    (rationalFunction_cyclicGaloisAlgebra_mem_center_iff_exists_place F L a ha x)

def rationalFunctionCyclicAlgebraCommutatorEquationRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x y : cyclicGaloisAlgebra (RatFunc F) L a) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_exists_commutator_eq_iff_forall_place F L a ha x y)
    (rationalFunction_cyclicGaloisAlgebra_exists_commutator_eq_iff_exists_place F L a ha x y)

def rationalFunctionCyclicAlgebraCentralizerFinrankRigidHassePredicate
    (a : RatFunc F) (ha : a ≠ 0) (x : cyclicGaloisAlgebra (RatFunc F) L a) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_forall_place F L a ha x d)
    (rationalFunction_cyclicGaloisAlgebra_centralizerFinrank_eq_iff_exists_place F L a ha x d)

end RationalFunction

end GaloisForLFunctions.HTGeometry.ABHN
