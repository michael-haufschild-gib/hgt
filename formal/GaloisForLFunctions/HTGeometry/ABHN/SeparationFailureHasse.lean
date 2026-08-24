import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseSeparation

/-!
# One-place separation and failures at every completion

Injectivity of every completed field embedding and every completed scalar-extension map gives
one-place certificates for equality. Dually, inequality and nonvanishing persist at every place.
No finite-dimensionality or central-simplicity assumption is required.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- Equality of number-field scalars can be certified at one completion. -/
theorem numberField_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (x y : K) :
    x = y ↔ ∃ w : NumberFieldPlace K,
      placeEmbedding K w x = placeEmbedding K w y := by
  constructor
  · rintro rfl
    exact ⟨witnessPlace K, rfl⟩
  · rintro ⟨w, hw⟩
    exact placeEmbedding_injective K w hw

/-- Equality of rational functions can be certified at one completion. -/
theorem rationalFunction_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (x y : RatFunc F) :
    x = y ↔ ∃ w : RationalFunctionPlace F,
      rationalFunctionPlaceEmbedding F w x = rationalFunctionPlaceEmbedding F w y := by
  constructor
  · rintro rfl
    exact ⟨.infinite, rfl⟩
  · rintro ⟨w, hw⟩
    exact rationalFunctionPlaceEmbedding_injective F w hw

/-- Equality of arbitrary number-field algebra elements can be certified at one completion. -/
theorem numberField_algebra_eq_iff_exists_localScalarExtension
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a b : A) :
    a = b ↔ ∃ w : NumberFieldPlace K,
      (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a =
        Algebra.TensorProduct.includeRight b := by
  constructor
  · rintro rfl
    exact ⟨witnessPlace K, rfl⟩
  · rintro ⟨w, hw⟩
    exact Algebra.TensorProduct.includeRight_injective
      (A := completion K w) (B := A)
      (FaithfulSMul.algebraMap_injective K (completion K w)) hw

/-- Equality of arbitrary `F(t)`-algebra elements can be certified at one completion. -/
theorem rationalFunction_algebra_eq_iff_exists_localScalarExtension
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a b : A) :
    a = b ↔ ∃ w : RationalFunctionPlace F,
      (Algebra.TensorProduct.includeRight :
        A →ₐ[RatFunc F] rationalFunctionCompletion F w ⊗[RatFunc F] A) a =
          Algebra.TensorProduct.includeRight b := by
  constructor
  · rintro rfl
    exact ⟨.infinite, rfl⟩
  · rintro ⟨w, hw⟩
    exact Algebra.TensorProduct.includeRight_injective
      (A := rationalFunctionCompletion F w) (B := A)
      (FaithfulSMul.algebraMap_injective (RatFunc F)
        (rationalFunctionCompletion F w)) hw

/-- Inequality of number-field scalars persists at every completion. -/
theorem numberField_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (x y : K) :
    x ≠ y ↔ ∀ w : NumberFieldPlace K,
      placeEmbedding K w x ≠ placeEmbedding K w y :=
  not_iff_forall_not_of_iff_exists (numberField_eq_iff_exists_place K x y)

/-- Inequality of rational functions persists at every completion. -/
theorem rationalFunction_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] (x y : RatFunc F) :
    x ≠ y ↔ ∀ w : RationalFunctionPlace F,
      rationalFunctionPlaceEmbedding F w x ≠ rationalFunctionPlaceEmbedding F w y :=
  not_iff_forall_not_of_iff_exists (rationalFunction_eq_iff_exists_place F x y)

/-- Inequality of arbitrary number-field algebra elements persists at every completion. -/
theorem numberField_algebra_ne_iff_forall_localScalarExtension
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a b : A) :
    a ≠ b ↔ ∀ w : NumberFieldPlace K,
      (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a ≠
        Algebra.TensorProduct.includeRight b :=
  not_iff_forall_not_of_iff_exists
    (numberField_algebra_eq_iff_exists_localScalarExtension K A a b)

/-- Inequality of arbitrary `F(t)`-algebra elements persists at every completion. -/
theorem rationalFunction_algebra_ne_iff_forall_localScalarExtension
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a b : A) :
    a ≠ b ↔ ∀ w : RationalFunctionPlace F,
      (Algebra.TensorProduct.includeRight :
        A →ₐ[RatFunc F] rationalFunctionCompletion F w ⊗[RatFunc F] A) a ≠
          Algebra.TensorProduct.includeRight b :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_algebra_eq_iff_exists_localScalarExtension F A a b)

/-- Nonvanishing of an arbitrary number-field algebra element persists at every completion. -/
theorem numberField_algebra_ne_zero_iff_forall_localScalarExtension
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a : A) :
    a ≠ 0 ↔ ∀ w : NumberFieldPlace K,
      (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a ≠ 0 := by
  simpa using numberField_algebra_ne_iff_forall_localScalarExtension K A a 0

/-- Nonvanishing of an arbitrary `F(t)`-algebra element persists at every completion. -/
theorem rationalFunction_algebra_ne_zero_iff_forall_localScalarExtension
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a : A) :
    a ≠ 0 ↔ ∀ w : RationalFunctionPlace F,
      (Algebra.TensorProduct.includeRight :
        A →ₐ[RatFunc F] rationalFunctionCompletion F w ⊗[RatFunc F] A) a ≠ 0 := by
  simpa using rationalFunction_algebra_ne_iff_forall_localScalarExtension F A a 0

end GaloisForLFunctions.HTGeometry.ABHN
