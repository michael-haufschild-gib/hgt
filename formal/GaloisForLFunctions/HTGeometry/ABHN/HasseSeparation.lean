/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.DiagonalScalarExtension

/-!
# Weak Hasse separation for fields and algebra elements

Global-field scalars and elements of arbitrary algebras over them are separated by completed
scalar extension.  These are element-level Hasse principles: equality and vanishing are equivalent
to equality and vanishing at every finite or infinite place.  No Azumaya or finite-dimensionality
assumption is needed.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- Number-field weak Hasse principle for equality of scalars. -/
theorem numberField_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (x y : K) :
    x = y ↔ ∀ w : NumberFieldPlace K,
      placeEmbedding K w x = placeEmbedding K w y := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro h
    apply placeDiagonal_injective K
    funext w
    exact h w

/-- A number-field scalar vanishes globally exactly when it vanishes in every completion. -/
theorem numberField_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (x : K) :
    x = 0 ↔ ∀ w : NumberFieldPlace K, placeEmbedding K w x = 0 := by
  simpa using numberField_eq_iff_forall_place K x 0

/-- Every nonzero number-field scalar remains nonzero at every completion. -/
theorem numberField_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (x : K) :
    x ≠ 0 ↔ ∀ w : NumberFieldPlace K, placeEmbedding K w x ≠ 0 := by
  constructor
  · intro hx w hw
    apply hx
    exact placeEmbedding_injective K w (by simpa using hw)
  · intro h hx
    simpa [hx] using h (witnessPlace K)

/-- Rational-function-field weak Hasse principle for equality of scalars. -/
theorem rationalFunction_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (x y : RatFunc F) :
    x = y ↔ ∀ w : RationalFunctionPlace F,
      rationalFunctionPlaceEmbedding F w x = rationalFunctionPlaceEmbedding F w y := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro h
    apply rationalFunctionPlaceDiagonal_injective F
    funext w
    exact h w

/-- A rational function vanishes globally exactly when it vanishes in every completion. -/
theorem rationalFunction_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (x : RatFunc F) :
    x = 0 ↔ ∀ w : RationalFunctionPlace F,
      rationalFunctionPlaceEmbedding F w x = 0 := by
  simpa using rationalFunction_eq_iff_forall_place F x 0

/-- Every nonzero rational function remains nonzero at every completion. -/
theorem rationalFunction_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (x : RatFunc F) :
    x ≠ 0 ↔ ∀ w : RationalFunctionPlace F,
      rationalFunctionPlaceEmbedding F w x ≠ 0 := by
  constructor
  · intro hx w hw
    apply hx
    exact rationalFunctionPlaceEmbedding_injective F w (by simpa using hw)
  · intro h hx
    simpa [hx] using h (.infinite : RationalFunctionPlace F)

/-- Number-field Hasse separation for elements of any algebra after scalar extension to every
completion. -/
theorem numberField_algebra_eq_iff_forall_localScalarExtension
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a b : A) :
    a = b ↔ ∀ w : NumberFieldPlace K,
      (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a =
        Algebra.TensorProduct.includeRight b := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro h
    let w := witnessPlace K
    exact Algebra.TensorProduct.includeRight_injective
      (A := completion K w) (B := A)
      (FaithfulSMul.algebraMap_injective K (completion K w)) (h w)

/-- A number-field algebra element is zero exactly when every completed scalar extension is zero. -/
theorem numberField_algebra_eq_zero_iff_forall_localScalarExtension
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a : A) :
    a = 0 ↔ ∀ w : NumberFieldPlace K,
      (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a = 0 := by
  simpa using numberField_algebra_eq_iff_forall_localScalarExtension K A a 0

/-- Function-field Hasse separation for elements of any algebra after scalar extension to every
completion. -/
theorem rationalFunction_algebra_eq_iff_forall_localScalarExtension
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a b : A) :
    a = b ↔ ∀ w : RationalFunctionPlace F,
      (Algebra.TensorProduct.includeRight :
        A →ₐ[RatFunc F] rationalFunctionCompletion F w ⊗[RatFunc F] A) a =
          Algebra.TensorProduct.includeRight b := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro h
    exact Algebra.TensorProduct.includeRight_injective
      (A := rationalFunctionCompletion F .infinite) (B := A)
      (FaithfulSMul.algebraMap_injective (RatFunc F)
        (rationalFunctionCompletion F .infinite)) (h .infinite)

/-- A function-field algebra element is zero exactly when every completed scalar extension is
zero. -/
theorem rationalFunction_algebra_eq_zero_iff_forall_localScalarExtension
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a : A) :
    a = 0 ↔ ∀ w : RationalFunctionPlace F,
      (Algebra.TensorProduct.includeRight :
        A →ₐ[RatFunc F] rationalFunctionCompletion F w ⊗[RatFunc F] A) a = 0 := by
  simpa using rationalFunction_algebra_eq_iff_forall_localScalarExtension F A a 0

end GaloisForLFunctions.HTGeometry.ABHN
