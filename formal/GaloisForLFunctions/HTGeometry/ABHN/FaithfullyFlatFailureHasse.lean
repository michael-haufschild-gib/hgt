import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness
import GaloisForLFunctions.HTGeometry.ABHN.HasseGeometricProperties
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutativity
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixNilpotence

/-!
# Persistence of faithfully-flat local obstructions

For properties reflected by every field extension, one completed place already detects the global
property.  These are rigid Hasse systems: failure is not confined to an exceptional place but
persists at every completion.  This module records that stronger contrapositive form for the two
global-field models used by the ABHN development.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Non-finiteness of a number-field module persists at every completion. -/
theorem numberField_module_not_finite_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] :
    ¬ Module.Finite K M ↔ ∀ p : NumberFieldPlace K,
      ¬ Module.Finite (completion K p) (completion K p ⊗[K] M) := by
  rw [numberField_module_finite_iff_exists_place]
  push Not
  rfl

/-- Non-finiteness of a rational-function module persists at every completion. -/
theorem rationalFunction_module_not_finite_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    ¬ Module.Finite (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      ¬ Module.Finite (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  rw [rationalFunction_module_finite_iff_exists_place]
  push Not
  rfl

/-- Failure of finite type over a number field persists at every completion. -/
theorem numberField_algebra_not_finiteType_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.FiniteType K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.FiniteType (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_finiteType_iff_exists_place]
  push Not
  rfl

/-- Failure of finite type over a rational function field persists at every completion. -/
theorem rationalFunction_algebra_not_finiteType_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.FiniteType (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.FiniteType (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_finiteType_iff_exists_place]
  push Not
  rfl

/-- Failure of finite presentation over a number field persists at every completion. -/
theorem numberField_algebra_not_finitePresentation_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.FinitePresentation K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.FinitePresentation (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_finitePresentation_iff_exists_place]
  push Not
  rfl

/-- Failure of finite presentation over a rational function field persists everywhere. -/
theorem rationalFunction_algebra_not_finitePresentation_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.FinitePresentation (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.FinitePresentation (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_finitePresentation_iff_exists_place]
  push Not
  rfl

/-- Nonsmoothness over a number field persists at every completion. -/
theorem numberField_algebra_not_smooth_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.Smooth K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.Smooth (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_smooth_iff_exists_place]
  push Not
  rfl

/-- Nonsmoothness over a rational function field persists at every completion. -/
theorem rationalFunction_algebra_not_smooth_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.Smooth (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.Smooth (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_smooth_iff_exists_place]
  push Not
  rfl

/-- Ramification of a number-field algebra persists at every completion in this scalar-extension
sense. -/
theorem numberField_algebra_not_unramified_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.Unramified K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.Unramified (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_unramified_iff_exists_place]
  push Not
  rfl

/-- Ramification of a rational-function algebra persists at every completion. -/
theorem rationalFunction_algebra_not_unramified_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.Unramified (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.Unramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_unramified_iff_exists_place]
  push Not
  rfl

/-- Non-étaleness over a number field persists at every completion. -/
theorem numberField_algebra_not_etale_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.Etale K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.Etale (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_etale_iff_exists_place]
  push Not
  rfl

/-- Non-étaleness over a rational function field persists at every completion. -/
theorem rationalFunction_algebra_not_etale_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.Etale (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.Etale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_etale_iff_exists_place]
  push Not
  rfl

/-- Failure of finite étaleness over a number field persists at every completion. -/
theorem numberField_algebra_not_finiteEtale_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] :
    ¬ Algebra.FiniteEtale K A ↔ ∀ p : NumberFieldPlace K,
      ¬ Algebra.FiniteEtale (completion K p) (completion K p ⊗[K] A) := by
  rw [numberField_algebra_finiteEtale_iff_exists_place]
  push Not
  rfl

/-- Failure of finite étaleness over a rational function field persists at every completion. -/
theorem rationalFunction_algebra_not_finiteEtale_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    ¬ Algebra.FiniteEtale (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      ¬ Algebra.FiniteEtale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  rw [rationalFunction_algebra_finiteEtale_iff_exists_place]
  push Not
  rfl

/-- Failure of a prescribed matrix-power relation persists at every number-field completion. -/
theorem numberFieldMatrix_pow_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    M ^ d ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))) ^ d ≠ 0 := by
  have h := not_congr (numberFieldMatrix_pow_eq_zero_iff_exists_place K n M d)
  simpa only [not_exists] using h

/-- Failure of a prescribed matrix-power relation persists at every function-field completion. -/
theorem rationalFunctionMatrix_pow_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :
    M ^ d ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) ^ d ≠ 0 := by
  have h := not_congr (rationalFunctionMatrix_pow_eq_zero_iff_exists_place F n M d)
  simpa only [not_exists] using h

/-- Failure of a prescribed unipotence exponent persists at every number-field completion. -/
theorem numberFieldMatrix_sub_one_pow_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (d : ℕ) :
    (M - 1) ^ d ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p)) - 1) ^ d ≠ 0 := by
  have h := not_congr
    (numberFieldMatrix_sub_one_pow_eq_zero_iff_exists_place K n M d)
  simpa only [not_exists] using h

/-- Failure of a prescribed unipotence exponent persists at every function-field completion. -/
theorem rationalFunctionMatrix_sub_one_pow_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) (d : ℕ) :
    (M - 1) ^ d ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) - 1) ^ d ≠ 0 := by
  have h := not_congr
    (rationalFunctionMatrix_sub_one_pow_eq_zero_iff_exists_place F n M d)
  simpa only [not_exists] using h

/-- Nonnilpotence of a matrix persists at every number-field completion. -/
theorem numberFieldMatrix_not_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    ¬ IsNilpotent M ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNilpotent (M.map (algebraMap K (completion K p))) := by
  rw [numberFieldMatrix_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- Nonnilpotence of a matrix persists at every function-field completion. -/
theorem rationalFunctionMatrix_not_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    ¬ IsNilpotent M ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNilpotent
        (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))) := by
  rw [rationalFunctionMatrix_isNilpotent_iff_exists_place]
  push Not
  rfl

/-- A number-field CSA is noncommutative exactly when every completion contains a noncommuting
pair. -/
theorem numberField_csa_noncommutative_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) :
    (∃ a b : A.carrier, a * b ≠ b * a) ↔
      ∀ p : NumberFieldPlace K,
        ∃ x y : completion K p ⊗[K] A.carrier, x * y ≠ y * x := by
  have h := not_congr (numberFieldLocalScalarExtensionMap_mul_comm_iff_exists_place K A)
  simpa only [not_forall, not_exists] using h

/-- A function-field CSA is noncommutative exactly when every completion contains a noncommuting
pair. -/
theorem rationalFunction_csa_noncommutative_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) :
    (∃ a b : A.carrier, a * b ≠ b * a) ↔
      ∀ p : RationalFunctionPlace F,
        ∃ x y : rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier,
          x * y ≠ y * x := by
  have h := not_congr
    (rationalFunctionLocalScalarExtensionMap_mul_comm_iff_exists_place F A)
  simpa only [not_forall, not_exists] using h

end GaloisForLFunctions.HTGeometry.ABHN
