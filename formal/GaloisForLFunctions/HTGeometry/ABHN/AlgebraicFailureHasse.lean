import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapNilpotence
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPowers
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraNilpotence
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRelations

/-!
# Persistence of algebraic relation failures at every completion

Faithful scalar extension reflects polynomial identities.  The contrapositive says that failures
of nilpotence, ideal-power identities, idempotence, finite-order matrix relations, commutation, and
semiconjugacy survive at every global-field completion.  This is the algebraic counterpart to
reciprocity support rigidity: these defects replicate rather than cancel between places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

/-- Nonnilpotence of a number-field endomorphism persists at every completion. -/
theorem numberField_linearMap_not_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (f : M →ₗ[K] M) :
    ¬ IsNilpotent f ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNilpotent (f.baseChange (completion K p)) := by
  rw [numberField_linearMap_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- Nonnilpotence of a function-field endomorphism persists at every completion. -/
theorem rationalFunction_linearMap_not_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (f : M →ₗ[RatFunc F] M) :
    ¬ IsNilpotent f ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNilpotent (f.baseChange (rationalFunctionCompletion F p)) := by
  rw [rationalFunction_linearMap_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- Failure of a number-field ideal-power identity persists at every completion. -/
theorem numberField_ideal_pow_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) (n : ℕ) :
    I ^ n ≠ J ↔ ∀ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ^ n ≠
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  have h := not_congr (numberField_ideal_pow_eq_iff_exists_place K I J n)
  simpa only [not_exists] using h

/-- Failure of a function-field ideal-power identity persists at every completion. -/
theorem rationalFunction_ideal_pow_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) (n : ℕ) :
    I ^ n ≠ J ↔ ∀ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ^ n ≠
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  have h := not_congr (rationalFunction_ideal_pow_eq_iff_exists_place F I J n)
  simpa only [not_exists] using h

/-- Nonidempotence of a number-field ideal persists at every completion. -/
theorem numberField_ideal_not_isIdempotentElem_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    ¬ IsIdempotentElem I ↔ ∀ p : NumberFieldPlace K,
      ¬ IsIdempotentElem (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  rw [numberField_ideal_isIdempotentElem_iff_exists_place K I]
  push Not
  rfl

/-- Nonidempotence of a function-field ideal persists at every completion. -/
theorem rationalFunction_ideal_not_isIdempotentElem_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    ¬ IsIdempotentElem I ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsIdempotentElem
        (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  rw [rationalFunction_ideal_isIdempotentElem_iff_exists_place F I]
  push Not
  rfl

/-- Nonnilpotence of a number-field ideal persists at every completion. -/
theorem numberField_ideal_not_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    ¬ IsNilpotent I ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNilpotent (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  rw [numberField_ideal_isNilpotent_iff_exists_place K I]
  push Not
  rfl

/-- Nonnilpotence of a function-field ideal persists at every completion. -/
theorem rationalFunction_ideal_not_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    ¬ IsNilpotent I ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNilpotent (I.map
        (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  rw [rationalFunction_ideal_isNilpotent_iff_exists_place F I]
  push Not
  rfl

/-- Nonnilpotence of an element of a number-field CSA persists at every completion. -/
theorem numberField_csaElement_not_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) (a : A.carrier) :
    ¬ IsNilpotent a ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNilpotent (numberFieldLocalScalarExtensionMap K p A a) := by
  rw [numberFieldLocalScalarExtensionMap_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- Nonnilpotence of an element of a function-field CSA persists at every completion. -/
theorem rationalFunction_csaElement_not_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    ¬ IsNilpotent a ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNilpotent (rationalFunctionLocalScalarExtensionMap F p A a) := by
  rw [rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- Failure of a prescribed finite-order relation persists at every number-field completion. -/
theorem numberFieldMatrix_pow_ne_one_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) (d : ℕ) :
    M ^ d ≠ 1 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))) ^ d ≠ 1 := by
  have h := not_congr (numberFieldMatrix_pow_eq_one_iff_exists_place K n M d)
  simpa only [not_exists] using h

/-- Failure of a prescribed finite-order relation persists at every function-field completion. -/
theorem rationalFunctionMatrix_pow_ne_one_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) (d : ℕ) :
    M ^ d ≠ 1 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) ^ d ≠ 1 := by
  have h := not_congr (rationalFunctionMatrix_pow_eq_one_iff_exists_place F n M d)
  simpa only [not_exists] using h

/-- Nonidempotence of a number-field matrix persists at every completion. -/
theorem numberFieldMatrix_not_isIdempotentElem_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    ¬ IsIdempotentElem M ↔ ∀ p : NumberFieldPlace K,
      ¬ IsIdempotentElem (M.map (algebraMap K (completion K p))) := by
  rw [numberFieldMatrix_isIdempotentElem_iff_exists_place]
  push Not
  rfl

/-- Nonidempotence of a function-field matrix persists at every completion. -/
theorem rationalFunctionMatrix_not_isIdempotentElem_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M : Matrix n n (RatFunc F)) :
    ¬ IsIdempotentElem M ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsIdempotentElem
        (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  rw [rationalFunctionMatrix_isIdempotentElem_iff_exists_place]
  push Not
  rfl

/-- Noncommutation of two number-field matrices persists at every completion. -/
theorem numberFieldMatrix_not_commute_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (M N : Matrix n n K) :
    ¬ Commute M N ↔ ∀ p : NumberFieldPlace K,
      ¬ Commute (M.map (algebraMap K (completion K p)))
        (N.map (algebraMap K (completion K p))) := by
  rw [numberFieldMatrix_commute_iff_exists_place]
  push Not
  rfl

/-- Noncommutation of two function-field matrices persists at every completion. -/
theorem rationalFunctionMatrix_not_commute_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (M N : Matrix n n (RatFunc F)) :
    ¬ Commute M N ↔ ∀ p : RationalFunctionPlace F,
      ¬ Commute (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (N.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  rw [rationalFunctionMatrix_commute_iff_exists_place]
  push Not
  rfl

/-- Failure of number-field matrix semiconjugacy persists at every completion. -/
theorem numberFieldMatrix_not_semiconjBy_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n] (A X Y : Matrix n n K) :
    ¬ SemiconjBy A X Y ↔ ∀ p : NumberFieldPlace K,
      ¬ SemiconjBy (A.map (algebraMap K (completion K p)))
        (X.map (algebraMap K (completion K p))) (Y.map (algebraMap K (completion K p))) := by
  rw [numberFieldMatrix_semiconjBy_iff_exists_place]
  push Not
  rfl

/-- Failure of function-field matrix semiconjugacy persists at every completion. -/
theorem rationalFunctionMatrix_not_semiconjBy_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n] (A X Y : Matrix n n (RatFunc F)) :
    ¬ SemiconjBy A X Y ↔ ∀ p : RationalFunctionPlace F,
      ¬ SemiconjBy (A.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (X.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)))
        (Y.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  rw [rationalFunctionMatrix_semiconjBy_iff_exists_place]
  push Not
  rfl

end GaloisForLFunctions.HTGeometry.ABHN
