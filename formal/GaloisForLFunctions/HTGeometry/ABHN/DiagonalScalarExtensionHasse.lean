import GaloisForLFunctions.HTGeometry.ABHN.DiagonalScalarExtension

/-!
# Hasse classification by simultaneous scalar extension

An algebra over a global field embeds into its simultaneous scalar extension to all completions.
Thus global algebra elements are equivalent to the all-place tensor profiles actually realized.
The construction requires no Azumaya or simplicity hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

open NumberField

/-- Simultaneous scalar extension of a number-field algebra, bundled as an algebra homomorphism. -/
noncomputable def numberFieldDiagonalTensorMap
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] :
    A →ₐ[K] TensorProduct K ((w : NumberFieldPlace K) → completion K w) A :=
  Algebra.TensorProduct.includeRight

/-- A number-field algebra is equivalent to the simultaneous all-completion tensor profiles it
actually realizes. -/
noncomputable def numberFieldDiagonalTensorHasseEquivRealizedProfiles
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] :
    A ≃ₐ[K] AlgHom.range (numberFieldDiagonalTensorMap K A) :=
  AlgEquiv.ofBijective
    (AlgHom.rangeRestrict (numberFieldDiagonalTensorMap K A))
    ⟨fun x y h => by
        apply numberFieldDiagonalTensor_includeRight_injective K A
        have hval := congrArg Subtype.val h
        change Algebra.TensorProduct.includeRight x =
          Algebra.TensorProduct.includeRight y at hval
        exact hval,
      AlgHom.rangeRestrict_surjective _⟩

/-- The realized-profile equivalence evaluates by simultaneous scalar extension. -/
@[simp] theorem numberFieldDiagonalTensorHasseEquivRealizedProfiles_apply
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a : A) :
    (numberFieldDiagonalTensorHasseEquivRealizedProfiles K A a).1 =
      numberFieldDiagonalTensorMap K A a := by
  rfl

/-- Number-field algebra elements are equal exactly when their simultaneous scalar extensions to
all completions agree. -/
theorem numberFieldDiagonalTensor_congr_hasse_iff
    (K : Type u) [Field K] [NumberField K]
    (A : Type v) [Ring A] [Algebra K A] (a b : A) :
    numberFieldDiagonalTensorMap K A a =
      numberFieldDiagonalTensorMap K A b ↔ a = b := by
  constructor
  · intro h
    apply numberFieldDiagonalTensor_includeRight_injective K A
    simpa only [numberFieldDiagonalTensorMap] using h
  · exact congrArg _

/-- Simultaneous scalar extension of a rational-function-field algebra, bundled as an algebra
homomorphism. -/
noncomputable def rationalFunctionDiagonalTensorMap
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] :
    A →ₐ[RatFunc F] TensorProduct (RatFunc F)
      ((w : RationalFunctionPlace F) → rationalFunctionCompletion F w) A :=
  Algebra.TensorProduct.includeRight

/-- A rational-function-field algebra is equivalent to the simultaneous all-place tensor profiles
it actually realizes. -/
noncomputable def rationalFunctionDiagonalTensorHasseEquivRealizedProfiles
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] :
    A ≃ₐ[RatFunc F] AlgHom.range (rationalFunctionDiagonalTensorMap F A) :=
  AlgEquiv.ofBijective
    (AlgHom.rangeRestrict (rationalFunctionDiagonalTensorMap F A))
    ⟨fun x y h => by
        apply rationalFunctionDiagonalTensor_includeRight_injective F A
        have hval := congrArg Subtype.val h
        change Algebra.TensorProduct.includeRight x =
          Algebra.TensorProduct.includeRight y at hval
        exact hval,
      AlgHom.rangeRestrict_surjective _⟩

/-- The rational-function realized-profile equivalence evaluates by simultaneous scalar
extension. -/
@[simp] theorem rationalFunctionDiagonalTensorHasseEquivRealizedProfiles_apply
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a : A) :
    (rationalFunctionDiagonalTensorHasseEquivRealizedProfiles F A a).1 =
      rationalFunctionDiagonalTensorMap F A a := by
  rfl

/-- Rational-function-field algebra elements are equal exactly when their simultaneous scalar
extensions to all places agree. -/
theorem rationalFunctionDiagonalTensor_congr_hasse_iff
    (F : Type u) [Field F] [Finite F]
    (A : Type v) [Ring A] [Algebra (RatFunc F) A] (a b : A) :
    rationalFunctionDiagonalTensorMap F A a =
      rationalFunctionDiagonalTensorMap F A b ↔ a = b := by
  constructor
  · intro h
    apply rationalFunctionDiagonalTensor_includeRight_injective F A
    simpa only [rationalFunctionDiagonalTensorMap] using h
  · exact congrArg _

end


end GaloisForLFunctions.HTGeometry.ABHN
