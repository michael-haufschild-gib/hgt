import GaloisForLFunctions.HTGeometry.ABHN.HasseDomain
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormAlternating
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealPrimary
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRadical
import GaloisForLFunctions.HTGeometry.ABHN.HasseLocalRing
import GaloisForLFunctions.HTGeometry.ABHN.HasseQuadraticForms

/-!
# One-way Hasse failure principles

Some properties descend from a faithfully flat scalar extension without ascending through every
field extension. For these properties, global failure still forces failure at every completion,
but the converse is not asserted. This covers domains, reduced rings, local rings, radical ideals,
and primary ideals.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A non-domain number-field algebra remains a non-domain at every completion. -/
theorem numberField_not_isDomain_implies_forall_place_not_isDomain
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (h : ¬ IsDomain A) :
    ∀ p : NumberFieldPlace K, ¬ IsDomain (completion K p ⊗[K] A) := by
  intro p hp
  exact h (numberField_isDomain_of_exists_place K ⟨p, hp⟩)

/-- A non-domain `F(t)`-algebra remains a non-domain at every completion. -/
theorem rationalFunction_not_isDomain_implies_forall_place_not_isDomain
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (h : ¬ IsDomain A) :
    ∀ p : RationalFunctionPlace F,
      ¬ IsDomain (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  intro p hp
  exact h (rationalFunction_isDomain_of_exists_place F ⟨p, hp⟩)

/-- A nonreduced number-field algebra remains nonreduced at every completion. -/
theorem numberField_not_isReduced_implies_forall_place_not_isReduced
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (h : ¬ IsReduced A) :
    ∀ p : NumberFieldPlace K, ¬ IsReduced (completion K p ⊗[K] A) := by
  intro p hp
  exact h (numberField_isReduced_of_exists_place K ⟨p, hp⟩)

/-- A nonreduced `F(t)`-algebra remains nonreduced at every completion. -/
theorem rationalFunction_not_isReduced_implies_forall_place_not_isReduced
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (h : ¬ IsReduced A) :
    ∀ p : RationalFunctionPlace F,
      ¬ IsReduced (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  intro p hp
  exact h (rationalFunction_isReduced_of_exists_place F ⟨p, hp⟩)

/-- A nonlocal number-field algebra remains nonlocal at every completion. -/
theorem numberField_not_isLocalRing_implies_forall_place_not_isLocalRing
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (h : ¬ IsLocalRing A) :
    ∀ p : NumberFieldPlace K, ¬ IsLocalRing (completion K p ⊗[K] A) := by
  intro p hp
  exact h (numberField_isLocalRing_of_exists_place K ⟨p, hp⟩)

/-- A nonlocal `F(t)`-algebra remains nonlocal at every completion. -/
theorem rationalFunction_not_isLocalRing_implies_forall_place_not_isLocalRing
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (h : ¬ IsLocalRing A) :
    ∀ p : RationalFunctionPlace F,
      ¬ IsLocalRing (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  intro p hp
  exact h (rationalFunction_isLocalRing_of_exists_place F ⟨p, hp⟩)

/-- Nonradicality of an ideal in a number-field algebra persists at every completion. -/
theorem numberField_ideal_not_isRadical_implies_forall_place_not_isRadical
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) (h : ¬ I.IsRadical) :
    ∀ p : NumberFieldPlace K,
      ¬ (I.map (algebraMap A (completion K p ⊗[K] A))).IsRadical := by
  intro p hp
  exact h (numberField_ideal_isRadical_of_exists_place K I ⟨p, hp⟩)

/-- Nonradicality of an ideal in an `F(t)`-algebra persists at every completion. -/
theorem rationalFunction_ideal_not_isRadical_implies_forall_place_not_isRadical
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (h : ¬ I.IsRadical) :
    ∀ p : RationalFunctionPlace F,
      ¬ (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsRadical := by
  intro p hp
  exact h (rationalFunction_ideal_isRadical_of_exists_place F I ⟨p, hp⟩)

/-- Nonprimality of an ideal in a number-field algebra persists at every completion. -/
theorem numberField_ideal_not_isPrime_implies_forall_place_not_isPrime
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) (h : ¬ I.IsPrime) :
    ∀ p : NumberFieldPlace K,
      ¬ (I.map (algebraMap A (completion K p ⊗[K] A))).IsPrime := by
  intro p hp
  exact h (numberField_ideal_isPrime_of_exists_place K I ⟨p, hp⟩)

/-- Nonprimality of an ideal in an `F(t)`-algebra persists at every completion. -/
theorem rationalFunction_ideal_not_isPrime_implies_forall_place_not_isPrime
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (h : ¬ I.IsPrime) :
    ∀ p : RationalFunctionPlace F,
      ¬ (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsPrime := by
  intro p hp
  exact h (rationalFunction_ideal_isPrime_of_exists_place F I ⟨p, hp⟩)

/-- Nonprimaryness of an ideal in a number-field algebra persists at every completion. -/
theorem numberField_ideal_not_isPrimary_implies_forall_place_not_isPrimary
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) (h : ¬ I.IsPrimary) :
    ∀ p : NumberFieldPlace K,
      ¬ (I.map (algebraMap A (completion K p ⊗[K] A))).IsPrimary := by
  intro p hp
  exact h (numberField_ideal_isPrimary_of_exists_place K I ⟨p, hp⟩)

/-- Nonprimaryness of an ideal in an `F(t)`-algebra persists at every completion. -/
theorem rationalFunction_ideal_not_isPrimary_implies_forall_place_not_isPrimary
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (h : ¬ I.IsPrimary) :
    ∀ p : RationalFunctionPlace F,
      ¬ (I.map (algebraMap A
        (rationalFunctionCompletion F p ⊗[RatFunc F] A))).IsPrimary := by
  intro p hp
  exact h (rationalFunction_ideal_isPrimary_of_exists_place F I ⟨p, hp⟩)

/-- Nonreflexivity of a number-field bilinear form persists at every completion. -/
theorem numberField_bilinForm_not_isRefl_implies_forall_place_not_isRefl
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : ¬ B.IsRefl) :
    ∀ p : NumberFieldPlace K, ¬ (B.baseChange (completion K p)).IsRefl := by
  intro p hp
  exact h (numberField_bilinForm_isRefl_of_exists_place K B ⟨p, hp⟩)

/-- Nonreflexivity of an `F(t)`-bilinear form persists at every completion. -/
theorem rationalFunction_bilinForm_not_isRefl_implies_forall_place_not_isRefl
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) (h : ¬ B.IsRefl) :
    ∀ p : RationalFunctionPlace F,
      ¬ (B.baseChange (rationalFunctionCompletion F p)).IsRefl := by
  intro p hp
  exact h (rationalFunction_bilinForm_isRefl_of_exists_place F B ⟨p, hp⟩)

/-- Failure of anisotropy for a number-field quadratic form persists at every completion. -/
theorem numberField_quadraticForm_not_anisotropic_implies_forall_place_not_anisotropic
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (h : ¬ Q.Anisotropic) :
    ∀ p : NumberFieldPlace K,
      ¬ (numberFieldQuadraticFormBaseChange K Q p).Anisotropic := by
  intro p hp
  exact h (numberField_quadraticForm_anisotropic_of_exists_place K Q ⟨p, hp⟩)

/-- Failure of anisotropy for an `F(t)`-quadratic form persists at every completion. -/
theorem rationalFunction_quadraticForm_not_anisotropic_implies_forall_place_not_anisotropic
    (F : Type u) [Field F] [Finite F] [Invertible (2 : RatFunc F)]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (Q : QuadraticForm (RatFunc F) M) (h : ¬ Q.Anisotropic) :
    ∀ p : RationalFunctionPlace F,
      ¬ (rationalFunctionQuadraticFormBaseChange F Q p).Anisotropic := by
  intro p hp
  exact h (rationalFunction_quadraticForm_anisotropic_of_exists_place F Q ⟨p, hp⟩)

end GaloisForLFunctions.HTGeometry.ABHN
