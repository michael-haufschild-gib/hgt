/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.PlaceDiagonalEquiv

/-!
# Simultaneous local scalar extension of Azumaya algebras

The diagonal of a global field into all of its completed local fields is an actual base ring for
one simultaneous scalar extension.  This file proves that the resulting algebra is Azumaya and
that its canonical map from the global algebra is injective.  Thus local scalar extension detects
global algebra elements jointly.  This is the algebra-level local--global separation behind ABHN;
it does not assert the deeper statement that local Brauer classes detect global Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- The canonical product algebra structure on all number-field completions is the Hasse
diagonal embedding. -/
theorem numberFieldPlaceDiagonalRingHom_eq_algebraMap
    (K : Type u) [Field K] [NumberField K] :
    numberFieldPlaceDiagonalRingHom K =
      algebraMap K ((w : NumberFieldPlace K) → completion K w) := by
  ext x w
  cases w with
  | finite v => rfl
  | infinite v => rfl

/-- The canonical product algebra structure on all rational-function-field completions is the
Hasse diagonal embedding. -/
theorem rationalFunctionPlaceDiagonalRingHom_eq_algebraMap
    (F : Type u) [Field F] [Finite F] :
    rationalFunctionPlaceDiagonalRingHom F =
      algebraMap (RatFunc F) ((w : RationalFunctionPlace F) → rationalFunctionCompletion F w) := by
  ext x w
  cases w with
  | finite v => rfl
  | infinite => rfl

/-- Project a simultaneous number-field scalar extension to one local scalar extension. -/
noncomputable def numberFieldDiagonalTensorProjection
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Semiring A] [Algebra K A] (w : NumberFieldPlace K) :
    ((z : NumberFieldPlace K) → completion K z) ⊗[K] A →ₐ[K]
      completion K w ⊗[K] A :=
  Algebra.TensorProduct.map
    (Pi.evalAlgHom K (fun z : NumberFieldPlace K => completion K z) w)
    (AlgHom.id K A)

/-- Projection to a number-field completion preserves the canonical scalar-extension map. -/
theorem numberFieldDiagonalTensorProjection_includeRight
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Semiring A] [Algebra K A]
    (w : NumberFieldPlace K) (a : A) :
    numberFieldDiagonalTensorProjection K A w
      (Algebra.TensorProduct.includeRight a) = Algebra.TensorProduct.includeRight a := by
  simp [numberFieldDiagonalTensorProjection]

/-- Simultaneous scalar extension to all number-field completions is injective on global algebra
elements, without an Azumaya hypothesis. -/
theorem numberFieldDiagonalTensor_includeRight_injective
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K]
        ((w : NumberFieldPlace K) → completion K w) ⊗[K] A) := by
  intro a b hab
  let w : NumberFieldPlace K := witnessPlace K
  have h := congrArg (numberFieldDiagonalTensorProjection K A w) hab
  change (Algebra.TensorProduct.includeRight : A →ₐ[K] completion K w ⊗[K] A) a =
    Algebra.TensorProduct.includeRight b at h
  exact Algebra.TensorProduct.includeRight_injective (A := completion K w) (B := A)
    (FaithfulSMul.algebraMap_injective K (completion K w)) h

/-- Simultaneous scalar extension of an Azumaya algebra to all number-field completions is
injective on its global algebra elements. -/
theorem numberFieldDiagonalScalarExtensionMap_injective
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] [IsAzumaya K A] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[K]
        ((w : NumberFieldPlace K) → completion K w) ⊗[K] A) := by
  exact numberFieldDiagonalTensor_includeRight_injective K A

/-- Simultaneous scalar extension along the number-field Hasse diagonal remains Azumaya. -/
theorem numberFieldDiagonalScalarExtension_isAzumaya
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] [IsAzumaya K A] :
    IsAzumaya ((w : NumberFieldPlace K) → completion K w)
      (((w : NumberFieldPlace K) → completion K w) ⊗[K] A) :=
  AzumayaScalarExtension.isAzumaya_scalarExtension
    (R := K) (S := (w : NumberFieldPlace K) → completion K w) (A := A)

/-- Project a simultaneous rational-function-field scalar extension to one local scalar
extension. -/
noncomputable def rationalFunctionDiagonalTensorProjection
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Semiring A] [Algebra (RatFunc F) A] (w : RationalFunctionPlace F) :
    ((z : RationalFunctionPlace F) → rationalFunctionCompletion F z) ⊗[RatFunc F] A →ₐ[RatFunc F]
      rationalFunctionCompletion F w ⊗[RatFunc F] A :=
  Algebra.TensorProduct.map
    (Pi.evalAlgHom (RatFunc F) (fun z : RationalFunctionPlace F =>
      rationalFunctionCompletion F z) w)
    (AlgHom.id (RatFunc F) A)

/-- Projection to a rational-function-field completion preserves the canonical scalar-extension
map. -/
theorem rationalFunctionDiagonalTensorProjection_includeRight
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Semiring A] [Algebra (RatFunc F) A]
    (w : RationalFunctionPlace F) (a : A) :
    rationalFunctionDiagonalTensorProjection F A w
      (Algebra.TensorProduct.includeRight a) = Algebra.TensorProduct.includeRight a := by
  simp [rationalFunctionDiagonalTensorProjection]

/-- Simultaneous scalar extension to all `F(t)`-completions is injective on global algebra
elements, without an Azumaya hypothesis. -/
theorem rationalFunctionDiagonalTensor_includeRight_injective
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[RatFunc F]
        ((w : RationalFunctionPlace F) → rationalFunctionCompletion F w) ⊗[RatFunc F] A) := by
  intro a b hab
  have h := congrArg (rationalFunctionDiagonalTensorProjection F A .infinite) hab
  change (Algebra.TensorProduct.includeRight : A →ₐ[RatFunc F]
      rationalFunctionCompletion F .infinite ⊗[RatFunc F] A) a =
    Algebra.TensorProduct.includeRight b at h
  exact Algebra.TensorProduct.includeRight_injective
    (A := rationalFunctionCompletion F .infinite) (B := A)
    (FaithfulSMul.algebraMap_injective (RatFunc F)
      (rationalFunctionCompletion F .infinite)) h

/-- Simultaneous scalar extension of an Azumaya algebra to all rational-function-field
completions is injective on its global algebra elements. -/
theorem rationalFunctionDiagonalScalarExtensionMap_injective
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] [IsAzumaya (RatFunc F) A] :
    Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[RatFunc F]
        ((w : RationalFunctionPlace F) → rationalFunctionCompletion F w) ⊗[RatFunc F] A) := by
  exact rationalFunctionDiagonalTensor_includeRight_injective F A

/-- Simultaneous scalar extension along the rational-function-field Hasse diagonal remains
Azumaya. -/
theorem rationalFunctionDiagonalScalarExtension_isAzumaya
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] [IsAzumaya (RatFunc F) A] :
    IsAzumaya ((w : RationalFunctionPlace F) → rationalFunctionCompletion F w)
      (((w : RationalFunctionPlace F) → rationalFunctionCompletion F w) ⊗[RatFunc F] A) :=
  AzumayaScalarExtension.isAzumaya_scalarExtension
    (R := RatFunc F) (S := (w : RationalFunctionPlace F) → rationalFunctionCompletion F w)
    (A := A)

end GaloisForLFunctions.HTGeometry.ABHN
