import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixDiagonal
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixSymmetry
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixNilpotence

/-!
# Rigid matrix-relation Hasse predicates

Specified matrix relations over global fields are reflected by every completion and any one
completion.  These predicates cover static matrix structure, polynomial dynamics, linear systems,
and matrix factorizations.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w z

def numberFieldMatrixDiagonalRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (n : Type v) (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_isDiag_iff_forall_place K n M)
    (numberFieldMatrix_isDiag_iff_exists_place K n M)

def rationalFunctionMatrixDiagonalRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (n : Type v) (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_isDiag_iff_forall_place F n M)
    (rationalFunctionMatrix_isDiag_iff_exists_place F n M)

def numberFieldMatrixSymmetricRigidHassePredicate
    (K : Type u) [Field K] [NumberField K] (n : Type v) (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_isSymm_iff_forall_place K n M)
    (numberFieldMatrix_isSymm_iff_exists_place K n M)

def rationalFunctionMatrixSymmetricRigidHassePredicate
    (F : Type u) [Field F] [Finite F] (n : Type v) (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_isSymm_iff_forall_place F n M)
    (rationalFunctionMatrix_isSymm_iff_exists_place F n M)

def numberFieldMatrixCommuteRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M N : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_commute_iff_forall_place K n M N)
    (numberFieldMatrix_commute_iff_exists_place K n M N)

def rationalFunctionMatrixCommuteRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M N : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_commute_iff_forall_place F n M N)
    (rationalFunctionMatrix_commute_iff_exists_place F n M N)

def numberFieldMatrixSemiconjugacyRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (A X Y : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_semiconjBy_iff_forall_place K n A X Y)
    (numberFieldMatrix_semiconjBy_iff_exists_place K n A X Y)

def rationalFunctionMatrixSemiconjugacyRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (A X Y : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_semiconjBy_iff_forall_place F n A X Y)
    (rationalFunctionMatrix_semiconjBy_iff_exists_place F n A X Y)

def numberFieldMatrixFiniteOrderRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_pow_eq_one_iff_forall_place K n M d)
    (numberFieldMatrix_pow_eq_one_iff_exists_place K n M d)

def rationalFunctionMatrixFiniteOrderRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_pow_eq_one_iff_forall_place F n M d)
    (rationalFunctionMatrix_pow_eq_one_iff_exists_place F n M d)

def numberFieldMatrixPowerVanishingRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_pow_eq_zero_iff_forall_place K n M d)
    (numberFieldMatrix_pow_eq_zero_iff_exists_place K n M d)

def rationalFunctionMatrixPowerVanishingRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_pow_eq_zero_iff_forall_place F n M d)
    (rationalFunctionMatrix_pow_eq_zero_iff_exists_place F n M d)

def numberFieldMatrixUnipotenceRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) (d : ℕ) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_sub_one_pow_eq_zero_iff_forall_place K n M d)
    (numberFieldMatrix_sub_one_pow_eq_zero_iff_exists_place K n M d)

def rationalFunctionMatrixUnipotenceRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_sub_one_pow_eq_zero_iff_forall_place F n M d)
    (rationalFunctionMatrix_sub_one_pow_eq_zero_iff_exists_place F n M d)

def numberFieldMatrixNilpotentRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_isNilpotent_iff_forall_place K n M)
    (numberFieldMatrix_isNilpotent_iff_exists_place K n M)

def rationalFunctionMatrixNilpotentRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (n : Type v) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_isNilpotent_iff_forall_place F n M)
    (rationalFunctionMatrix_isNilpotent_iff_exists_place F n M)

def numberFieldMatrixMulVecRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ K) (x : κ → K) (b : ι → K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_mulVec_eq_iff_forall_place K ι κ A x b)
    (numberFieldMatrix_mulVec_eq_iff_exists_place K ι κ A x b)

def rationalFunctionMatrixMulVecRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (x : κ → RatFunc F) (b : ι → RatFunc F) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_mulVec_eq_iff_forall_place F ι κ A x b)
    (rationalFunctionMatrix_mulVec_eq_iff_exists_place F ι κ A x b)

def numberFieldMatrixMultiplicationRigidHassePredicate
    (K : Type u) [Field K] [NumberField K]
    (ι : Type v) (κ : Type w) (o : Type z) [Fintype κ]
    (A : Matrix ι κ K) (B : Matrix κ o K) (C : Matrix ι o K) :=
  RigidHassePredicate.fixed
    (numberFieldMatrix_mul_eq_iff_forall_place K ι κ o A B C)
    (numberFieldMatrix_mul_eq_iff_exists_place K ι κ o A B C)

def rationalFunctionMatrixMultiplicationRigidHassePredicate
    (F : Type u) [Field F] [Finite F]
    (ι : Type v) (κ : Type w) (o : Type z) [Fintype κ]
    (A : Matrix ι κ (RatFunc F)) (B : Matrix κ o (RatFunc F))
    (C : Matrix ι o (RatFunc F)) :=
  RigidHassePredicate.fixed
    (rationalFunctionMatrix_mul_eq_iff_forall_place F ι κ o A B C)
    (rationalFunctionMatrix_mul_eq_iff_exists_place F ι κ o A B C)

end GaloisForLFunctions.HTGeometry.ABHN
