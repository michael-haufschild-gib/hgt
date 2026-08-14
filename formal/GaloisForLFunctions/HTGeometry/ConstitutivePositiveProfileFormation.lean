import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Data.Complex.Basic

/-!
# Positive receiver profiles under split star formation

This module formalizes the positive-representation face of common-recovery formation mechanics.

* every star-algebra map can only shrink the receiver profile of a source element;
* a star-algebra recovery makes that inclusion an equality;
* receiver-relative positive invisibility is therefore exactly conserved;
* an equivariant split formation preserves functional-equation fixedness on its image;
* any star-isotropic source element remains invisible after every direct star-algebra formation
  into a positive C-star receiver.

The last statement is an exact selection no-go: positive visibility cannot be manufactured by a
direct star-homomorphic completion of the existing reflected-orthogonal source law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A B C : Type*}
  [Semiring A] [Star A] [Algebra ℂ A]
  [Semiring B] [Star B] [Algebra ℂ B]
  [Semiring C] [Star C] [Algebra ℂ C]

/-- A star-algebra formation equipped with a star-algebra recovery. -/
structure SplitStarFormation (A B : Type*)
    [Semiring A] [Star A] [Algebra ℂ A]
    [Semiring B] [Star B] [Algebra ℂ B] where
  form : A →⋆ₐ[ℂ] B
  recover : B →⋆ₐ[ℂ] A
  recover_form : Function.LeftInverse recover form

/-- Values of one source element across all star-algebra maps into a fixed receiver. -/
def starReceiverProfile (C : Type*) [Semiring C] [Star C] [Algebra ℂ C]
    (x : A) : Set C :=
  {z | ∃ π : A →⋆ₐ[ℂ] C, π x = z}

/-- An element is invisible in a receiver when every star-algebra map kills it. -/
def StarReceiverInvisible (C : Type*) [Semiring C] [Star C] [Algebra ℂ C]
    (x : A) : Prop :=
  ∀ π : A →⋆ₐ[ℂ] C, π x = 0

/-- A split formation is injective. -/
theorem SplitStarFormation.form_injective (E : SplitStarFormation A B) :
    Function.Injective E.form :=
  E.recover_form.injective

/-- Any star-algebra formation can only shrink a fixed receiver profile. -/
theorem starReceiverProfile_map_subset (F : A →⋆ₐ[ℂ] B) (x : A) :
    starReceiverProfile C (F x) ⊆ starReceiverProfile C x := by
  rintro z ⟨π, rfl⟩
  exact ⟨π.comp F, rfl⟩

/-- Split recovery upgrades profile data processing to exact profile conservation. -/
theorem SplitStarFormation.starReceiverProfile_form
    (E : SplitStarFormation A B) (x : A) :
    starReceiverProfile C (E.form x) = starReceiverProfile C x := by
  apply Set.Subset.antisymm
  · exact starReceiverProfile_map_subset E.form x
  · rintro z ⟨φ, rfl⟩
    refine ⟨φ.comp E.recover, ?_⟩
    simpa using congrArg φ (E.recover_form x)

/-- Exact receiver-radical pullback under split formation. -/
theorem SplitStarFormation.starReceiverInvisible_form_iff
    (E : SplitStarFormation A B) (x : A) :
    StarReceiverInvisible C (E.form x) ↔ StarReceiverInvisible C x := by
  constructor
  · intro h φ
    rw [← E.recover_form x]
    exact h (φ.comp E.recover)
  · intro h π
    exact h (π.comp E.form)

/-- Equivariant split formation carries a pair of functional-equation actions. -/
structure FunctionalSplitStarFormation (A B : Type*)
    [Semiring A] [Star A] [Algebra ℂ A]
    [Semiring B] [Star B] [Algebra ℂ B] where
  split : SplitStarFormation A B
  sourceAction : A → A
  formedAction : B → B
  source_involutive : Function.Involutive sourceAction
  formed_involutive : Function.Involutive formedAction
  equivariant : ∀ x, split.form (sourceAction x) = formedAction (split.form x)

/-- Equivariant split formation preserves the functional-equation fixed locus on its image. -/
theorem FunctionalSplitStarFormation.formed_fixed_iff_source_fixed
    (E : FunctionalSplitStarFormation A B) (x : A) :
    E.formedAction (E.split.form x) = E.split.form x ↔ E.sourceAction x = x := by
  constructor
  · intro h
    apply E.split.form_injective
    rw [E.equivariant, h]
  · intro h
    rw [← E.equivariant, h]

/-- Joint split-formation neutrality: receiver profile, radical, and functional fixedness are all
preserved by the same recovery structure. -/
theorem FunctionalSplitStarFormation.profile_radical_fixedness_neutral
    (E : FunctionalSplitStarFormation A B) (x : A) :
    starReceiverProfile C (E.split.form x) = starReceiverProfile C x ∧
      (StarReceiverInvisible C (E.split.form x) ↔ StarReceiverInvisible C x) ∧
      (E.formedAction (E.split.form x) = E.split.form x ↔ E.sourceAction x = x) := by
  exact ⟨E.split.starReceiverProfile_form x,
    E.split.starReceiverInvisible_form_iff x,
    E.formed_fixed_iff_source_fixed x⟩

section CStar

variable {A₁ B₁ D : Type*}
  [Semiring A₁] [StarRing A₁] [Algebra ℂ A₁]
  [Semiring B₁] [StarRing B₁] [Algebra ℂ B₁]
  [NormedRing D] [StarRing D] [CStarRing D] [Algebra ℂ D]

/-- Any direct star-algebra formation of a star-isotropic source element remains invisible in every
positive C-star receiver. -/
theorem starAlgHom_kills_formed_starIsotropic
    (F : A₁ →⋆ₐ[ℂ] B₁) (π : B₁ →⋆ₐ[ℂ] D) {x : A₁}
    (hx : star x * x = 0) :
    π (F x) = 0 := by
  rw [← CStarRing.star_mul_self_eq_zero_iff (π (F x))]
  rw [← map_star π, ← map_mul, ← map_star F, ← map_mul, hx, map_zero, map_zero]

end CStar

end

end GaloisForLFunctions.HTGeometry
