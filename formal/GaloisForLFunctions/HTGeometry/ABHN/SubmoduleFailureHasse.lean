import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleMembership
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRelations
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleStrictness
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleQuotients

/-!
# Submodule defects at every completion

Faithful completion reflects dimensions, membership, containment, equality, strict containment,
and quotient dimensions of fixed submodules.  Failure of any such condition persists at every
global-field place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A wrong number-field submodule dimension persists at every completion. -/
theorem numberField_submodule_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :
    Module.finrank K P ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (P.baseChange (completion K p)) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_finrank_eq_iff_exists_place K P n)

/-- A wrong function-field submodule dimension persists at every completion. -/
theorem rationalFunction_submodule_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :
    Module.finrank (RatFunc F) P ≠ n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (P.baseChange (rationalFunctionCompletion F p)) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_finrank_eq_iff_exists_place F P n)

/-- Failure of a linear constraint on a number-field CSA element persists everywhere. -/
theorem numberFieldLocalScalarExtensionMap_not_mem_baseChange_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (P : Submodule K A.carrier) (a : A.carrier) :
    a ∉ P ↔ ∀ p : NumberFieldPlace K,
      numberFieldLocalScalarExtensionMap K p A a ∉ P.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberFieldLocalScalarExtensionMap_mem_baseChange_iff_exists_place K A P a)

/-- Failure of a linear constraint on a function-field CSA element persists everywhere. -/
theorem rationalFunctionLocalScalarExtensionMap_not_mem_baseChange_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (P : Submodule (RatFunc F) A.carrier) (a : A.carrier) :
    a ∉ P ↔ ∀ p : RationalFunctionPlace F,
      rationalFunctionLocalScalarExtensionMap F p A a ∉
        P.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunctionLocalScalarExtensionMap_mem_baseChange_iff_exists_place F A P a)

/-- Failed containment of number-field submodules persists at every completion. -/
theorem numberField_submodule_not_le_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type v} [AddCommGroup M] [Module K M] (P Q : Submodule K M) :
    ¬ P ≤ Q ↔ ∀ p : NumberFieldPlace K,
      ¬ P.baseChange (completion K p) ≤ Q.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_le_iff_exists_place K P Q)

/-- Failed containment of function-field submodules persists at every completion. -/
theorem rationalFunction_submodule_not_le_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    ¬ P ≤ Q ↔ ∀ p : RationalFunctionPlace F,
      ¬ P.baseChange (rationalFunctionCompletion F p) ≤
        Q.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_le_iff_exists_place F P Q)

/-- Inequality of number-field submodules persists at every completion. -/
theorem numberField_submodule_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type v} [AddCommGroup M] [Module K M] (P Q : Submodule K M) :
    P ≠ Q ↔ ∀ p : NumberFieldPlace K,
      P.baseChange (completion K p) ≠ Q.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_eq_iff_exists_place K P Q)

/-- Inequality of function-field submodules persists at every completion. -/
theorem rationalFunction_submodule_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type v} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    P ≠ Q ↔ ∀ p : RationalFunctionPlace F,
      P.baseChange (rationalFunctionCompletion F p) ≠
        Q.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_eq_iff_exists_place F P Q)

/-- Failure of strict containment between number-field submodules persists everywhere. -/
theorem numberField_submodule_not_lt_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (P Q : Submodule K M) :
    ¬ P < Q ↔ ∀ p : NumberFieldPlace K,
      ¬ P.baseChange (completion K p) < Q.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_lt_iff_exists_place K P Q)

/-- Failure of strict containment between function-field submodules persists everywhere. -/
theorem rationalFunction_submodule_not_lt_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P Q : Submodule (RatFunc F) M) :
    ¬ P < Q ↔ ∀ p : RationalFunctionPlace F,
      ¬ P.baseChange (rationalFunctionCompletion F p) <
        Q.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_lt_iff_exists_place F P Q)

/-- A wrong quotient dimension of a number-field submodule persists everywhere. -/
theorem numberField_submodule_quotient_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (P : Submodule K M) (n : ℕ) :
    Module.finrank K (M ⧸ P) ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p)
        ((completion K p ⊗[K] M) ⧸ P.baseChange (completion K p)) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_quotient_finrank_eq_iff_exists_place K P n)

/-- A wrong quotient dimension of a function-field submodule persists everywhere. -/
theorem rationalFunction_submodule_quotient_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (P : Submodule (RatFunc F) M) (n : ℕ) :
    Module.finrank (RatFunc F) (M ⧸ P) ≠ n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        ((rationalFunctionCompletion F p ⊗[RatFunc F] M) ⧸
          P.baseChange (rationalFunctionCompletion F p)) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_quotient_finrank_eq_iff_exists_place F P n)

end GaloisForLFunctions.HTGeometry.ABHN
