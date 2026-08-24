import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraMembership
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraGeneration
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraContainment
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubalgebraStrictness
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealMembership
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealRelations

/-!
# Subalgebra and ideal defects at every completion

Faithful completion reflects fixed subalgebra membership, generation and containment, together
with ideal membership, containment and equality.  Failure of these multiplicative and congruence
conditions persists at every global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Nonmembership in a number-field CSA subalgebra persists at every completion. -/
theorem numberFieldLocalScalarExtensionMap_not_mem_subalgebraBaseChange_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (C : Subalgebra K A.carrier) (a : A.carrier) :
    a ∉ C ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∉ C.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_exists_place K A C a)

/-- Nonmembership in a function-field CSA subalgebra persists at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_not_mem_subalgebraBaseChange_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (C : Subalgebra (RatFunc F) A.carrier) (a : A.carrier) :
    a ∉ C ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∉
        C.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_mem_subalgebraBaseChange_iff_exists_place F A C a)

/-- Failure to generate a number-field algebra persists at every completion. -/
theorem numberField_subalgebra_ne_top_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] (C : Subalgebra K A) :
    C ≠ ⊤ ↔ ∀ p : NumberFieldPlace K, C.baseChange (completion K p) ≠ ⊤ :=
  not_iff_forall_not_of_iff_exists
    (numberField_subalgebra_eq_top_iff_exists_place K C)

/-- Failure to generate a function-field algebra persists at every completion. -/
theorem rationalFunction_subalgebra_ne_top_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A] (C : Subalgebra (RatFunc F) A) :
    C ≠ ⊤ ↔ ∀ p : RationalFunctionPlace F,
      C.baseChange (rationalFunctionCompletion F p) ≠ ⊤ :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_subalgebra_eq_top_iff_exists_place F C)

/-- Failed containment of number-field subalgebras persists at every completion. -/
theorem numberField_subalgebra_not_le_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] (C D : Subalgebra K A) :
    ¬ C ≤ D ↔ ∀ p : NumberFieldPlace K,
      ¬ C.baseChange (completion K p) ≤ D.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_subalgebra_le_iff_exists_place K C D)

/-- Failed containment of function-field subalgebras persists at every completion. -/
theorem rationalFunction_subalgebra_not_le_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) :
    ¬ C ≤ D ↔ ∀ p : RationalFunctionPlace F,
      ¬ C.baseChange (rationalFunctionCompletion F p) ≤
        D.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_subalgebra_le_iff_exists_place F C D)

/-- Failure of strict containment between number-field subalgebras persists everywhere. -/
theorem numberField_subalgebra_not_lt_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [Ring A] [Algebra K A] (C D : Subalgebra K A) :
    ¬ C < D ↔ ∀ p : NumberFieldPlace K,
      ¬ C.baseChange (completion K p) < D.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_subalgebra_lt_iff_exists_place K C D)

/-- Failure of strict containment between function-field subalgebras persists everywhere. -/
theorem rationalFunction_subalgebra_not_lt_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [Ring A] [Algebra (RatFunc F) A]
    (C D : Subalgebra (RatFunc F) A) :
    ¬ C < D ↔ ∀ p : RationalFunctionPlace F,
      ¬ C.baseChange (rationalFunctionCompletion F p) <
        D.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_subalgebra_lt_iff_exists_place F C D)

/-- Failure of a number-field ideal congruence persists at every completion. -/
theorem numberField_ideal_not_mem_map_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) (a : A) :
    a ∉ I ↔ ∀ p : NumberFieldPlace K,
      algebraMap A (completion K p ⊗[K] A) a ∉
        I.map (algebraMap A (completion K p ⊗[K] A)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_ideal_mem_map_iff_exists_place K I a)

/-- Failure of a function-field ideal congruence persists at every completion. -/
theorem rationalFunction_ideal_not_mem_map_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) (a : A) :
    a ∉ I ↔ ∀ p : RationalFunctionPlace F,
      algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A) a ∉
        I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_ideal_mem_map_iff_exists_place F I a)

/-- Failed containment of ideals in a number-field algebra persists everywhere. -/
theorem numberField_ideal_map_not_le_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    ¬ I ≤ J ↔ ∀ p : NumberFieldPlace K,
      ¬ I.map (algebraMap A (completion K p ⊗[K] A)) ≤
        J.map (algebraMap A (completion K p ⊗[K] A)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_ideal_map_le_iff_exists_place K I J)

/-- Failed containment of ideals in a function-field algebra persists everywhere. -/
theorem rationalFunction_ideal_map_not_le_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    ¬ I ≤ J ↔ ∀ p : RationalFunctionPlace F,
      ¬ I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ≤
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_ideal_map_le_iff_exists_place F I J)

/-- Inequality of ideals in a number-field algebra persists at every completion. -/
theorem numberField_ideal_map_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    I ≠ J ↔ ∀ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ≠
        J.map (algebraMap A (completion K p ⊗[K] A)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_ideal_map_eq_iff_exists_place K I J)

/-- Inequality of ideals in a function-field algebra persists at every completion. -/
theorem rationalFunction_ideal_map_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    I ≠ J ↔ ∀ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ≠
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_ideal_map_eq_iff_exists_place F I J)

end GaloisForLFunctions.HTGeometry.ABHN
