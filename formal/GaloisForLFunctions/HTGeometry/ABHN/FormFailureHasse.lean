import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseQuadraticForms
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormSymmetry
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormAlternating
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormNondegenerate

/-!
# Quadratic- and bilinear-form defects at every completion

Completed scalar extension reflects equality, nondegeneracy, fixed-vector isotropy, orthogonality,
symmetry, and alternation of forms.  Negating the corresponding one-place certificates shows that
each defect is simultaneously present at every global-field completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- Inequality of number-field quadratic forms persists at every completion. -/
theorem numberField_quadraticForm_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (Q₁ Q₂ : QuadraticForm K M) :
    Q₁ ≠ Q₂ ↔ ∀ p : NumberFieldPlace K,
      numberFieldQuadraticFormBaseChange K Q₁ p ≠ numberFieldQuadraticFormBaseChange K Q₂ p :=
  not_iff_forall_not_of_iff_exists
    (numberField_quadraticForm_eq_iff_exists_place K Q₁ Q₂)

/-- Inequality of `F(t)`-quadratic forms persists at every completion. -/
theorem rationalFunction_quadraticForm_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q₁ Q₂ : QuadraticForm (RatFunc F) M) :
    Q₁ ≠ Q₂ ↔ ∀ p : RationalFunctionPlace F,
      Q₁.baseChange (rationalFunctionCompletion F p) ≠
        Q₂.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_quadraticForm_eq_iff_exists_place F Q₁ Q₂)

/-- Degeneracy of a number-field quadratic form persists at every completion. -/
theorem numberField_quadraticForm_degenerate_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (Q : QuadraticForm K M) :
    ¬ Q.Nondegenerate ↔ ∀ p : NumberFieldPlace K,
      ¬ (numberFieldQuadraticFormBaseChange K Q p).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (numberField_quadraticForm_nondegenerate_iff_exists_place K Q)

/-- Degeneracy of an `F(t)`-quadratic form persists at every completion. -/
theorem rationalFunction_quadraticForm_degenerate_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [FiniteDimensional (RatFunc F) M] (Q : QuadraticForm (RatFunc F) M) :
    ¬ Q.Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      ¬ (rationalFunctionQuadraticFormBaseChange F Q p).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_quadraticForm_nondegenerate_iff_exists_place F Q)

/-- Nonvanishing of a fixed number-field quadratic-form value persists everywhere. -/
theorem numberField_quadraticForm_apply_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :
    Q x ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      numberFieldQuadraticFormBaseChange K Q p (1 ⊗ₜ[K] x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_quadraticForm_apply_eq_zero_iff_exists_place K Q x)

/-- Nonvanishing of a fixed `F(t)`-quadratic-form value persists everywhere. -/
theorem rationalFunction_quadraticForm_apply_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :
    Q x ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionQuadraticFormBaseChange F Q p (1 ⊗ₜ[RatFunc F] x) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_quadraticForm_apply_eq_zero_iff_exists_place F Q x)

/-- Failure of a fixed vector to be nonzero isotropic persists over all number-field places. -/
theorem numberField_quadraticForm_not_isotropicVector_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (Q : QuadraticForm K M) (x : M) :
    ¬ (x ≠ 0 ∧ Q x = 0) ↔ ∀ p : NumberFieldPlace K,
      ¬ ((1 ⊗ₜ[K] x : completion K p ⊗[K] M) ≠ 0 ∧
        numberFieldQuadraticFormBaseChange K Q p (1 ⊗ₜ[K] x) = 0) :=
  not_iff_forall_not_of_iff_exists
    (numberField_quadraticForm_isotropicVector_iff_exists_place K Q x)

/-- Failure of a fixed vector to be nonzero isotropic persists over all `F(t)` places. -/
theorem rationalFunction_quadraticForm_not_isotropicVector_iff_forall_place
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (x : M) :
    ¬ (x ≠ 0 ∧ Q x = 0) ↔ ∀ p : RationalFunctionPlace F,
      ¬ ((1 ⊗ₜ[RatFunc F] x : rationalFunctionCompletion F p ⊗[RatFunc F] M) ≠ 0 ∧
        rationalFunctionQuadraticFormBaseChange F Q p (1 ⊗ₜ[RatFunc F] x) = 0) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_quadraticForm_isotropicVector_iff_exists_place F Q x)

/-- Inequality of number-field bilinear forms persists at every completion. -/
theorem numberField_bilinForm_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (B C : LinearMap.BilinForm K M) :
    B ≠ C ↔ ∀ p : NumberFieldPlace K,
      B.baseChange (completion K p) ≠ C.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_bilinForm_eq_iff_exists_place K B C)

/-- Inequality of `F(t)`-bilinear forms persists at every completion. -/
theorem rationalFunction_bilinForm_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B C : LinearMap.BilinForm (RatFunc F) M) :
    B ≠ C ↔ ∀ p : RationalFunctionPlace F,
      B.baseChange (rationalFunctionCompletion F p) ≠
        C.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_bilinForm_eq_iff_exists_place F B C)

/-- Nonorthogonality of fixed number-field vectors persists at every completion. -/
theorem numberField_bilinForm_apply_ne_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (x y : M) :
    B x y ≠ 0 ↔ ∀ p : NumberFieldPlace K,
      B.baseChange (completion K p) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (numberField_bilinForm_apply_eq_zero_iff_exists_place K B x y)

/-- Nonorthogonality of fixed `F(t)`-vectors persists at every completion. -/
theorem rationalFunction_bilinForm_apply_ne_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) (x y : M) :
    B x y ≠ 0 ↔ ∀ p : RationalFunctionPlace F,
      B.baseChange (rationalFunctionCompletion F p)
        (1 ⊗ₜ[RatFunc F] x) (1 ⊗ₜ[RatFunc F] y) ≠ 0 :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_bilinForm_apply_eq_zero_iff_exists_place F B x y)

/-- Nonsymmetry of a number-field bilinear form persists at every completion. -/
theorem numberField_bilinForm_not_isSymm_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (B : LinearMap.BilinForm K M) :
    ¬ B.IsSymm ↔ ∀ p : NumberFieldPlace K,
      ¬ (B.baseChange (completion K p)).IsSymm :=
  not_iff_forall_not_of_iff_exists
    (numberField_bilinForm_isSymm_iff_exists_place K B)

/-- Nonsymmetry of an `F(t)`-bilinear form persists at every completion. -/
theorem rationalFunction_bilinForm_not_isSymm_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :
    ¬ B.IsSymm ↔ ∀ p : RationalFunctionPlace F,
      ¬ (B.baseChange (rationalFunctionCompletion F p)).IsSymm :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_bilinForm_isSymm_iff_exists_place F B)

/-- Nonalternation of a number-field bilinear form persists at every completion. -/
theorem numberField_bilinForm_not_isAlt_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (B : LinearMap.BilinForm K M) :
    ¬ B.IsAlt ↔ ∀ p : NumberFieldPlace K,
      ¬ (B.baseChange (completion K p)).IsAlt :=
  not_iff_forall_not_of_iff_exists
    (numberField_bilinForm_isAlt_iff_exists_place K B)

/-- Nonalternation of an `F(t)`-bilinear form persists at every completion. -/
theorem rationalFunction_bilinForm_not_isAlt_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :
    ¬ B.IsAlt ↔ ∀ p : RationalFunctionPlace F,
      ¬ (B.baseChange (rationalFunctionCompletion F p)).IsAlt :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_bilinForm_isAlt_iff_exists_place F B)

/-- Degeneracy of a number-field bilinear form persists at every completion. -/
theorem numberField_bilinForm_degenerate_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (B : LinearMap.BilinForm K M) :
    ¬ B.Nondegenerate ↔ ∀ p : NumberFieldPlace K,
      ¬ (B.baseChange (completion K p)).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (numberField_bilinForm_nondegenerate_iff_exists_place K B)

/-- Degeneracy of an `F(t)`-bilinear form persists at every completion. -/
theorem rationalFunction_bilinForm_degenerate_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [FiniteDimensional (RatFunc F) M] (B : LinearMap.BilinForm (RatFunc F) M) :
    ¬ B.Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      ¬ (B.baseChange (rationalFunctionCompletion F p)).Nondegenerate :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_bilinForm_nondegenerate_iff_exists_place F B)

end GaloisForLFunctions.HTGeometry.ABHN
