import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapCokernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEqualizers
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRanges
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapKernels
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions

/-!
# Linear-map structural defects at every completion

Faithful completion reflects cokernel dimensions, prescribed equalizers, ranges and kernels,
operator equality, and kernel/range dimensions.  Their failures persist at every global-field
place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- A wrong cokernel dimension over a number field persists at every completion. -/
theorem numberField_linearMap_cokernel_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (N ⧸ LinearMap.range f) ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p)
        ((completion K p ⊗[K] N) ⧸ LinearMap.range (f.baseChange (completion K p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_cokernel_finrank_eq_iff_exists_place K f n)

/-- A wrong cokernel dimension over a function field persists at every completion. -/
theorem rationalFunction_linearMap_cokernel_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (N ⧸ LinearMap.range f) ≠ n ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] N) ⧸
            LinearMap.range (f.baseChange (rationalFunctionCompletion F p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_cokernel_finrank_eq_iff_exists_place F f n)

/-- Failure of a prescribed number-field equalizer persists at every completion. -/
theorem numberField_submodule_ne_eqLocus_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N]
    (S : Submodule K M) (f g : M →ₗ[K] N) :
    S ≠ LinearMap.eqLocus f g ↔ ∀ p : NumberFieldPlace K,
      S.baseChange (completion K p) ≠
        LinearMap.eqLocus (f.baseChange (completion K p)) (g.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_eq_eqLocus_iff_exists_place K S f g)

/-- Failure of a prescribed function-field equalizer persists at every completion. -/
theorem rationalFunction_submodule_ne_eqLocus_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N]
    (S : Submodule (RatFunc F) M) (f g : M →ₗ[RatFunc F] N) :
    S ≠ LinearMap.eqLocus f g ↔ ∀ p : RationalFunctionPlace F,
      S.baseChange (rationalFunctionCompletion F p) ≠
        LinearMap.eqLocus (f.baseChange (rationalFunctionCompletion F p))
          (g.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_eq_eqLocus_iff_exists_place F S f g)

/-- Failure of a prescribed number-field range persists at every completion. -/
theorem numberField_submodule_ne_range_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (T : Submodule K N) (f : M →ₗ[K] N) :
    T ≠ LinearMap.range f ↔ ∀ p : NumberFieldPlace K,
      T.baseChange (completion K p) ≠ LinearMap.range (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_eq_range_iff_exists_place K T f)

/-- Failure of a prescribed function-field range persists at every completion. -/
theorem rationalFunction_submodule_ne_range_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N]
    (T : Submodule (RatFunc F) N) (f : M →ₗ[RatFunc F] N) :
    T ≠ LinearMap.range f ↔ ∀ p : RationalFunctionPlace F,
      T.baseChange (rationalFunctionCompletion F p) ≠
        LinearMap.range (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_eq_range_iff_exists_place F T f)

/-- Failure of a prescribed number-field kernel persists at every completion. -/
theorem numberField_submodule_ne_ker_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (S : Submodule K M) (f : M →ₗ[K] N) :
    S ≠ LinearMap.ker f ↔ ∀ p : NumberFieldPlace K,
      S.baseChange (completion K p) ≠ LinearMap.ker (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists
    (numberField_submodule_eq_ker_iff_exists_place K S f)

/-- Failure of a prescribed function-field kernel persists at every completion. -/
theorem rationalFunction_submodule_ne_ker_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N]
    (S : Submodule (RatFunc F) M) (f : M →ₗ[RatFunc F] N) :
    S ≠ LinearMap.ker f ↔ ∀ p : RationalFunctionPlace F,
      S.baseChange (rationalFunctionCompletion F p) ≠
        LinearMap.ker (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_submodule_eq_ker_iff_exists_place F S f)

/-- Inequality of number-field linear maps persists at every completion. -/
theorem numberField_linearMap_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f g : M →ₗ[K] N) :
    f ≠ g ↔ ∀ p : NumberFieldPlace K,
      f.baseChange (completion K p) ≠ g.baseChange (completion K p) :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_eq_iff_exists_place K f g)

/-- Inequality of function-field linear maps persists at every completion. -/
theorem rationalFunction_linearMap_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f g : M →ₗ[RatFunc F] N) :
    f ≠ g ↔ ∀ p : RationalFunctionPlace F,
      f.baseChange (rationalFunctionCompletion F p) ≠
        g.baseChange (rationalFunctionCompletion F p) :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_eq_iff_exists_place F f g)

/-- A wrong kernel dimension over a number field persists at every completion. -/
theorem numberField_linearMap_ker_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.ker f) ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.ker (f.baseChange (completion K p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_ker_finrank_eq_iff_exists_place K f n)

/-- A wrong range dimension over a number field persists at every completion. -/
theorem numberField_linearMap_range_finrank_ne_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.range f) ≠ n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.range (f.baseChange (completion K p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (numberField_linearMap_range_finrank_eq_iff_exists_place K f n)

/-- A wrong kernel dimension over a function field persists at every completion. -/
theorem rationalFunction_linearMap_ker_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker f) ≠ n ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (f.baseChange (rationalFunctionCompletion F p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_ker_finrank_eq_iff_exists_place F f n)

/-- A wrong range dimension over a function field persists at every completion. -/
theorem rationalFunction_linearMap_range_finrank_ne_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} {N : Type x} [AddCommGroup M] [Module (RatFunc F) M]
    [AddCommGroup N] [Module (RatFunc F) N] (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.range f) ≠ n ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.range (f.baseChange (rationalFunctionCompletion F p))) ≠ n :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_range_finrank_eq_iff_exists_place F f n)

end GaloisForLFunctions.HTGeometry.ABHN
