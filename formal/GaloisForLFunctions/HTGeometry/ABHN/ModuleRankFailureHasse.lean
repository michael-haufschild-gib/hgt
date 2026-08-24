import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks

/-!
# Module finrank failures at every completion

A prescribed finite-dimensional size is unchanged by completed scalar extension. Consequently,
failure of a proposed module finrank persists at every place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u w

/-- Failure of a prescribed number-field module finrank persists at every completion. -/
theorem numberField_module_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] (n : ℕ) :
    Module.finrank K M ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (completion K p ⊗[K] M) ≠ n :=
  not_iff_forall_not_of_iff_exists (numberField_module_finrank_eq_iff_exists_place K n)

/-- Failure of a prescribed `F(t)`-module finrank persists at every completion. -/
theorem rationalFunction_module_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] (n : ℕ) :
    Module.finrank (RatFunc F) M ≠ n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) ≠ n :=
  not_iff_forall_not_of_iff_exists (rationalFunction_module_finrank_eq_iff_exists_place F n)

end GaloisForLFunctions.HTGeometry.ABHN
