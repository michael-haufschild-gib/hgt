import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraMembership

/-!
# Subalgebra inequality at every completion

Equality of fixed subalgebras is reflected by any field scalar extension. This supplies
one-place equality certificates and the dual statement that distinct subalgebras remain distinct
at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u w

/-- Equality of number-field subalgebras can be certified at one completion. -/
theorem numberField_subalgebra_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] (C D : Subalgebra K A) :
    C = D ↔ ∃ p : NumberFieldPlace K,
      C.baseChange (completion K p) = D.baseChange (completion K p) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (subalgebra_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) C D).mp h⟩
  · rintro ⟨p, hp⟩
    exact (subalgebra_eq_iff_baseChange_eq (L := completion K p) C D).mpr hp

/-- Equality of `F(t)`-subalgebras can be certified at one completion. -/
theorem rationalFunction_subalgebra_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) :
    C = D ↔ ∃ p : RationalFunctionPlace F,
      C.baseChange (rationalFunctionCompletion F p) =
        D.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h
    exact ⟨.infinite, (subalgebra_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) C D).mp h⟩
  · rintro ⟨p, hp⟩
    exact (subalgebra_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F p) C D).mpr hp

/-- Distinct number-field subalgebras remain distinct at every completion. -/
theorem numberField_subalgebra_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] (C D : Subalgebra K A) :
    C ≠ D ↔ ∀ p : NumberFieldPlace K,
      C.baseChange (completion K p) ≠ D.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists (numberField_subalgebra_eq_iff_exists_place K C D)

/-- Distinct `F(t)`-subalgebras remain distinct at every completion. -/
theorem rationalFunction_subalgebra_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) :
    C ≠ D ↔ ∀ p : RationalFunctionPlace F,
      C.baseChange (rationalFunctionCompletion F p) ≠
        D.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_subalgebra_eq_iff_exists_place F C D)

end GaloisForLFunctions.HTGeometry.ABHN
