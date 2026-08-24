import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.HTGeometry.ABHN.HasseArtinian
import GaloisForLFunctions.HTGeometry.ABHN.HasseNoetherian
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleFlat
import GaloisForLFunctions.HTGeometry.ABHN.HasseSimpleModules
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealFiniteness
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealCoprime

/-!
# Module and ideal defects at every completion

Artinianity, Noetherianity, flatness, simplicity, finite generation of ideals, and ideal
coprimality are reflected by completed scalar extension in the global-field models.  Their
failures therefore persist at every place, providing rigid local certificates for module- and
scheme-theoretic defects.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u w

/-- Non-Artinianity of a number-field module persists at every completion. -/
theorem numberField_module_not_isArtinian_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] :
    ¬ IsArtinian K M ↔ ∀ p : NumberFieldPlace K,
      ¬ IsArtinian (completion K p) (completion K p ⊗[K] M) :=
  not_iff_forall_not_of_iff_exists (numberField_module_isArtinian_iff_exists_place K)

/-- Non-Artinianity of a function-field module persists at every completion. -/
theorem rationalFunction_module_not_isArtinian_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    ¬ IsArtinian (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsArtinian (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_module_isArtinian_iff_exists_place F)

/-- Non-Noetherianity of a number-field module persists at every completion. -/
theorem numberField_module_not_isNoetherian_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] :
    ¬ IsNoetherian K M ↔ ∀ p : NumberFieldPlace K,
      ¬ IsNoetherian (completion K p) (completion K p ⊗[K] M) :=
  not_iff_forall_not_of_iff_exists (numberField_module_isNoetherian_iff_exists_place K)

/-- Non-Noetherianity of a function-field module persists at every completion. -/
theorem rationalFunction_module_not_isNoetherian_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    ¬ IsNoetherian (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsNoetherian (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_module_isNoetherian_iff_exists_place F)

/-- Nonflatness of a number-field module persists at every completion. -/
theorem numberField_module_not_flat_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] :
    ¬ Module.Flat K M ↔ ∀ p : NumberFieldPlace K,
      ¬ Module.Flat (completion K p) (completion K p ⊗[K] M) :=
  not_iff_forall_not_of_iff_exists (numberField_module_flat_iff_exists_place K)

/-- Nonflatness of a function-field module persists at every completion. -/
theorem rationalFunction_module_not_flat_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    ¬ Module.Flat (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      ¬ Module.Flat (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_module_flat_iff_exists_place F)

/-- Nonsimplicity of a number-field module persists at every completion. -/
theorem numberField_module_not_isSimpleModule_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M] :
    ¬ IsSimpleModule K M ↔ ∀ p : NumberFieldPlace K,
      ¬ IsSimpleModule (completion K p) (completion K p ⊗[K] M) :=
  not_iff_forall_not_of_iff_exists (numberField_isSimpleModule_iff_exists_place K)

/-- Nonsimplicity of a function-field module persists at every completion. -/
theorem rationalFunction_module_not_isSimpleModule_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    ¬ IsSimpleModule (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsSimpleModule (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_isSimpleModule_iff_exists_place F)

/-- Failure of finite generation for a number-field ideal persists at every completion. -/
theorem numberField_ideal_not_fg_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    ¬ I.FG ↔ ∀ p : NumberFieldPlace K,
      ¬ (I.map (algebraMap A (completion K p ⊗[K] A))).FG :=
  not_iff_forall_not_of_iff_exists (numberField_ideal_fg_iff_exists_place K I)

/-- Failure of finite generation for a function-field ideal persists at every completion. -/
theorem rationalFunction_ideal_not_fg_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    ¬ I.FG ↔ ∀ p : RationalFunctionPlace F,
      ¬ (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))).FG :=
  not_iff_forall_not_of_iff_exists (rationalFunction_ideal_fg_iff_exists_place F I)

/-- Noncoprimality of number-field ideals persists at every completion. -/
theorem numberField_ideal_not_isCoprime_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    {A : Type w} [CommRing A] [Algebra K A] (I J : Ideal A) :
    ¬ IsCoprime I J ↔ ∀ p : NumberFieldPlace K,
      ¬ IsCoprime (I.map (algebraMap A (completion K p ⊗[K] A)))
        (J.map (algebraMap A (completion K p ⊗[K] A))) :=
  not_iff_forall_not_of_iff_exists (numberField_ideal_isCoprime_iff_exists_place K I J)

/-- Noncoprimality of function-field ideals persists at every completion. -/
theorem rationalFunction_ideal_not_isCoprime_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I J : Ideal A) :
    ¬ IsCoprime I J ↔ ∀ p : RationalFunctionPlace F,
      ¬ IsCoprime (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)))
        (J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) :=
  not_iff_forall_not_of_iff_exists (rationalFunction_ideal_isCoprime_iff_exists_place F I J)

end GaloisForLFunctions.HTGeometry.ABHN
