import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapSolvability
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapExactness
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence
import GaloisForLFunctions.HTGeometry.ABHN.HasseBasisFamily
import GaloisForLFunctions.HTGeometry.ABHN.HasseSpanning

/-!
# Linear-algebra defects at every completion

Completed scalar extension faithfully reflects injectivity, surjectivity, exactness, solvability,
linear independence, and spanning.  The negative forms below make every failure simultaneously
visible at all places.  They supply local obstruction statements for complexes, presentations,
spectral eigenspaces, and finite-dimensional realizations.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x y

/-- Noninjectivity of a number-field linear map persists at every completion. -/
theorem numberFieldLinearMap_not_injective_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    ¬ Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Injective (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists (numberFieldLinearMap_injective_iff_exists_place K f)

/-- Nonsurjectivity of a number-field linear map persists at every completion. -/
theorem numberFieldLinearMap_not_surjective_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    ¬ Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Surjective (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists (numberFieldLinearMap_surjective_iff_exists_place K f)

/-- Nonbijectivity of a number-field linear map persists at every completion. -/
theorem numberFieldLinearMap_not_bijective_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    ¬ Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Bijective (f.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists (numberFieldLinearMap_bijective_iff_exists_place K f)

/-- Noninjectivity of a function-field linear map persists at every completion. -/
theorem rationalFunctionLinearMap_not_injective_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    ¬ Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Injective (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists (rationalFunctionLinearMap_injective_iff_exists_place F f)

/-- Nonsurjectivity of a function-field linear map persists at every completion. -/
theorem rationalFunctionLinearMap_not_surjective_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    ¬ Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Surjective (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists (rationalFunctionLinearMap_surjective_iff_exists_place F f)

/-- Nonbijectivity of a function-field linear map persists at every completion. -/
theorem rationalFunctionLinearMap_not_bijective_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    ¬ Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Bijective (f.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists (rationalFunctionLinearMap_bijective_iff_exists_place F f)

/-- An unsolvable number-field linear equation stays unsolvable at every completion. -/
theorem numberField_linearMap_no_preimage_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (z : N) :
    (¬ ∃ x, f x = z) ↔ ∀ p : NumberFieldPlace K, ¬ ∃ y,
      f.baseChange (completion K p) y = (1 : completion K p) ⊗ₜ[K] z :=
  not_iff_forall_not_of_iff_exists (numberField_linearMap_exists_preimage_iff_exists_place K f z)

/-- An unsolvable function-field linear equation stays unsolvable at every completion. -/
theorem rationalFunction_linearMap_no_preimage_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (z : N) :
    (¬ ∃ x, f x = z) ↔ ∀ p : RationalFunctionPlace F, ¬ ∃ y,
      f.baseChange (rationalFunctionCompletion F p) y =
        (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] z :=
  not_iff_forall_not_of_iff_exists
    (rationalFunction_linearMap_exists_preimage_iff_exists_place F f z)

/-- Failure of exactness of a number-field linear complex persists at every completion. -/
theorem numberFieldLinearMap_not_exact_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P) :
    ¬ Function.Exact f g ↔ ∀ p : NumberFieldPlace K,
      ¬ Function.Exact (f.baseChange (completion K p)) (g.baseChange (completion K p)) :=
  not_iff_forall_not_of_iff_exists (numberFieldLinearMap_exact_iff_exists_place K f g)

/-- Failure of exactness of a function-field linear complex persists at every completion. -/
theorem rationalFunctionLinearMap_not_exact_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    [AddCommGroup P] [Module (RatFunc F) P]
    (f : M →ₗ[RatFunc F] N) (g : N →ₗ[RatFunc F] P) :
    ¬ Function.Exact f g ↔ ∀ p : RationalFunctionPlace F,
      ¬ Function.Exact (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p)) :=
  not_iff_forall_not_of_iff_exists (rationalFunctionLinearMap_exact_iff_exists_place F f g)

/-- Linear dependence over a number field persists at every completion. -/
theorem numberField_linearDependent_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] {ι : Type x} (v : ι → M) :
    ¬ LinearIndependent K v ↔ ∀ p : NumberFieldPlace K,
      ¬ LinearIndependent (completion K p) (fun i ↦ (1 : completion K p) ⊗ₜ[K] v i) :=
  not_iff_forall_not_of_iff_exists (numberField_linearIndependent_iff_exists_place K v)

/-- Linear dependence over `F(t)` persists at every completion. -/
theorem rationalFunction_linearDependent_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] {ι : Type x} (v : ι → M) :
    ¬ LinearIndependent (RatFunc F) v ↔ ∀ p : RationalFunctionPlace F,
      ¬ LinearIndependent (rationalFunctionCompletion F p)
        (fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] v i) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_linearIndependent_iff_exists_place F v)

/-- Failure of a family to be a number-field basis persists at every completion. -/
theorem numberField_not_basisFamily_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module K M] (b : ι → M) :
    ¬ (LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤) ↔
      ∀ p : NumberFieldPlace K,
        ¬ (LinearIndependent (completion K p) (fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) ∧
          Submodule.span (completion K p)
            (Set.range fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) = ⊤) :=
  not_iff_forall_not_of_iff_exists (numberField_basisFamily_iff_exists_place K b)

/-- Failure of a family to be an `F(t)`-basis persists at every completion. -/
theorem rationalFunction_not_basisFamily_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] (b : ι → M) :
    ¬ (LinearIndependent (RatFunc F) b ∧ Submodule.span (RatFunc F) (Set.range b) = ⊤) ↔
      ∀ p : RationalFunctionPlace F,
        ¬ (LinearIndependent (rationalFunctionCompletion F p)
          (fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) ∧
          Submodule.span (rationalFunctionCompletion F p)
            (Set.range fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) = ⊤) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_basisFamily_iff_exists_place F b)

/-- Failure of a number-field family to span persists at every completion. -/
theorem numberField_span_range_ne_top_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] {ι : Type x} (v : ι → M) :
    Submodule.span K (Set.range v) ≠ ⊤ ↔ ∀ p : NumberFieldPlace K,
      Submodule.span (completion K p)
        (Set.range fun i ↦ (1 : completion K p) ⊗ₜ[K] v i) ≠ ⊤ :=
  not_iff_forall_not_of_iff_exists (numberField_span_range_eq_top_iff_exists_place K v)

/-- Failure of a function-field family to span persists at every completion. -/
theorem rationalFunction_span_range_ne_top_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] {ι : Type x} (v : ι → M) :
    Submodule.span (RatFunc F) (Set.range v) ≠ ⊤ ↔ ∀ p : RationalFunctionPlace F,
      Submodule.span (rationalFunctionCompletion F p)
        (Set.range fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] v i) ≠ ⊤ :=
  not_iff_forall_not_of_iff_exists (rationalFunction_span_range_eq_top_iff_exists_place F v)

end GaloisForLFunctions.HTGeometry.ABHN
