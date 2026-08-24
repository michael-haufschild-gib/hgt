import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraHomEquality

/-!
# Algebra-homomorphism failures at every completion

Faithful scalar extension reflects equality, commutativity of fixed algebraic diagrams, equality
of algebra equivalences, and injectivity/surjectivity/bijectivity. This file adds one-place
certificates for the equality predicates and then records their failure duals at every place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- Equality of number-field algebra homomorphisms can be certified at one completion. -/
theorem numberField_algHom_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f g : A →ₐ[K] B) :
    f = g ↔ ∃ p : NumberFieldPlace K,
      algHomBaseChange (L := completion K p) f = algHomBaseChange (L := completion K p) g := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algHom_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) f g).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_eq_iff_baseChange_eq (L := completion K p) f g).mpr hp

/-- Equality of `F(t)`-algebra homomorphisms can be certified at one completion. -/
theorem rationalFunction_algHom_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f g : A →ₐ[RatFunc F] B) :
    f = g ↔ ∃ p : RationalFunctionPlace F,
      algHomBaseChange (L := rationalFunctionCompletion F p) f =
        algHomBaseChange (L := rationalFunctionCompletion F p) g := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algHom_eq_iff_baseChange_eq (L := rationalFunctionCompletion F .infinite) f g).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algHom_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) f g).mpr hp

/-- Commutativity of a fixed number-field algebraic diagram can be certified at one completion. -/
theorem numberField_algHom_comp_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Ring C] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) (h : A →ₐ[K] C) :
    g.comp f = h ↔ ∃ p : NumberFieldPlace K,
      (algHomBaseChange (L := completion K p) g).comp
          (algHomBaseChange (L := completion K p) f) =
        algHomBaseChange (L := completion K p) h := by
  constructor
  · intro hcomp
    exact ⟨witnessPlace K, (algHom_comp_eq_iff_baseChange_comp_eq
      (L := completion K (witnessPlace K)) f g h).mp hcomp⟩
  · rintro ⟨p, hp⟩
    exact (algHom_comp_eq_iff_baseChange_comp_eq (L := completion K p) f g h).mpr hp

/-- Commutativity of a fixed `F(t)`-algebraic diagram can be certified at one completion. -/
theorem rationalFunction_algHom_comp_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    [Ring C] [Algebra (RatFunc F) C]
    (f : A →ₐ[RatFunc F] B) (g : B →ₐ[RatFunc F] C) (h : A →ₐ[RatFunc F] C) :
    g.comp f = h ↔ ∃ p : RationalFunctionPlace F,
      (algHomBaseChange (L := rationalFunctionCompletion F p) g).comp
          (algHomBaseChange (L := rationalFunctionCompletion F p) f) =
        algHomBaseChange (L := rationalFunctionCompletion F p) h := by
  constructor
  · intro hcomp
    exact ⟨.infinite, (algHom_comp_eq_iff_baseChange_comp_eq
      (L := rationalFunctionCompletion F .infinite) f g h).mp hcomp⟩
  · rintro ⟨p, hp⟩
    exact (algHom_comp_eq_iff_baseChange_comp_eq
      (L := rationalFunctionCompletion F p) f g h).mpr hp

/-- Equality of number-field algebra equivalences can be certified at one completion. -/
theorem numberField_algEquiv_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (e f : A ≃ₐ[K] B) :
    e = f ↔ ∃ p : NumberFieldPlace K,
      algEquivBaseChange (L := completion K p) e =
        algEquivBaseChange (L := completion K p) f := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algEquiv_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) e f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algEquiv_eq_iff_baseChange_eq (L := completion K p) e f).mpr hp

/-- Equality of `F(t)`-algebra equivalences can be certified at one completion. -/
theorem rationalFunction_algEquiv_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (e f : A ≃ₐ[RatFunc F] B) :
    e = f ↔ ∃ p : RationalFunctionPlace F,
      algEquivBaseChange (L := rationalFunctionCompletion F p) e =
        algEquivBaseChange (L := rationalFunctionCompletion F p) f := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algEquiv_eq_iff_baseChange_eq (L := rationalFunctionCompletion F .infinite) e f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algEquiv_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) e f).mpr hp

/-- Inequality of number-field algebra homomorphisms persists at every completion. -/
theorem numberField_algHom_ne_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f g : A →ₐ[K] B) :
    f ≠ g ↔ ∀ p : NumberFieldPlace K,
      algHomBaseChange (L := completion K p) f ≠ algHomBaseChange (L := completion K p) g :=
  not_iff_forall_not_of_iff_exists (numberField_algHom_eq_iff_exists_place K f g)

/-- Inequality of `F(t)`-algebra homomorphisms persists at every completion. -/
theorem rationalFunction_algHom_ne_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f g : A →ₐ[RatFunc F] B) :
    f ≠ g ↔ ∀ p : RationalFunctionPlace F,
      algHomBaseChange (L := rationalFunctionCompletion F p) f ≠
        algHomBaseChange (L := rationalFunctionCompletion F p) g :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algHom_eq_iff_exists_place F f g)

/-- Failure of a number-field algebraic diagram to commute persists at every completion. -/
theorem numberField_algHom_comp_ne_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] [Ring C] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) (h : A →ₐ[K] C) :
    g.comp f ≠ h ↔ ∀ p : NumberFieldPlace K,
      (algHomBaseChange (L := completion K p) g).comp
          (algHomBaseChange (L := completion K p) f) ≠
        algHomBaseChange (L := completion K p) h :=
  not_iff_forall_not_of_iff_exists (numberField_algHom_comp_eq_iff_exists_place K f g h)

/-- Failure of an `F(t)`-algebraic diagram to commute persists at every completion. -/
theorem rationalFunction_algHom_comp_ne_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w} {C : Type x}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    [Ring C] [Algebra (RatFunc F) C]
    (f : A →ₐ[RatFunc F] B) (g : B →ₐ[RatFunc F] C) (h : A →ₐ[RatFunc F] C) :
    g.comp f ≠ h ↔ ∀ p : RationalFunctionPlace F,
      (algHomBaseChange (L := rationalFunctionCompletion F p) g).comp
          (algHomBaseChange (L := rationalFunctionCompletion F p) f) ≠
        algHomBaseChange (L := rationalFunctionCompletion F p) h :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algHom_comp_eq_iff_exists_place F f g h)

/-- Inequality of number-field algebra equivalences persists at every completion. -/
theorem numberField_algEquiv_ne_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (e f : A ≃ₐ[K] B) :
    e ≠ f ↔ ∀ p : NumberFieldPlace K,
      algEquivBaseChange (L := completion K p) e ≠
        algEquivBaseChange (L := completion K p) f :=
  not_iff_forall_not_of_iff_exists (numberField_algEquiv_eq_iff_exists_place K e f)

/-- Inequality of `F(t)`-algebra equivalences persists at every completion. -/
theorem rationalFunction_algEquiv_ne_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (e f : A ≃ₐ[RatFunc F] B) :
    e ≠ f ↔ ∀ p : RationalFunctionPlace F,
      algEquivBaseChange (L := rationalFunctionCompletion F p) e ≠
        algEquivBaseChange (L := rationalFunctionCompletion F p) f :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algEquiv_eq_iff_exists_place F e f)

/-- Noninjectivity of a number-field algebra homomorphism persists at every completion. -/
theorem numberField_algHom_not_injective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    ¬ Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Injective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists (numberField_algHom_injective_iff_exists_place K f)

/-- Noninjectivity of an `F(t)`-algebra homomorphism persists at every completion. -/
theorem rationalFunction_algHom_not_injective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    ¬ Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Injective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algHom_injective_iff_exists_place F f)

/-- Nonsurjectivity of a number-field algebra homomorphism persists at every completion. -/
theorem numberField_algHom_not_surjective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    ¬ Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Surjective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists (numberField_algHom_surjective_iff_exists_place K f)

/-- Nonsurjectivity of an `F(t)`-algebra homomorphism persists at every completion. -/
theorem rationalFunction_algHom_not_surjective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    ¬ Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Surjective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algHom_surjective_iff_exists_place F f)

/-- Nonbijectivity of a number-field algebra homomorphism persists at every completion. -/
theorem numberField_algHom_not_bijective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B] (f : A →ₐ[K] B) :
    ¬ Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Bijective (algHomBaseChange (L := completion K p) f) :=
  not_iff_forall_not_of_iff_exists (numberField_algHom_bijective_iff_exists_place K f)

/-- Nonbijectivity of an `F(t)`-algebra homomorphism persists at every completion. -/
theorem rationalFunction_algHom_not_bijective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f : A →ₐ[RatFunc F] B) :
    ¬ Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Bijective (algHomBaseChange (L := rationalFunctionCompletion F p) f) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_algHom_bijective_iff_exists_place F f)

end GaloisForLFunctions.HTGeometry.ABHN
