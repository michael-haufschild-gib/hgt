import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Spreading a generic linear isomorphism to a principal open set

For a domain, a map between finite/presented modules which is invertible at the
generic localization is already invertible after inverting one nonzero element.
This is the linear-algebraic finite-support mechanism needed to spread the
generic Azumaya left-right isomorphism of an order.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsLocalizedModule
open scoped TensorProduct

universe u v w z

/-- Bijectivity after tensoring with a fraction field is equivalent to bijectivity at the
generic localization. -/
theorem generic_localized_bijective_of_fractionField_baseChange_bijective
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hbij : Function.Bijective (f.baseChange K)) :
    Function.Bijective (IsLocalizedModule.map (⊥ : Ideal R).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl M)
      (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl N) f) := by
  rw [Ideal.primeCompl_bot]
  let S := nonZeroDivisors R
  let mM := LocalizedModule.mkLinearMap S M
  let mN := LocalizedModule.mkLinearMap S N
  let tM := TensorProduct.mk R K M 1
  let tN := TensorProduct.mk R K N 1
  let eM := IsLocalizedModule.linearEquiv S mM tM
  let eN := IsLocalizedModule.linearEquiv S mN tN
  let g := IsLocalizedModule.map S mM mN f
  have hcomp : eN.toLinearMap ∘ₗ g =
      (f.baseChange K).restrictScalars R ∘ₗ eM.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S mM tN
    exact LinearMap.ext fun x => by
      change eN (g (mM x)) = (f.baseChange K) (eM (mM x))
      rw [IsLocalizedModule.map_apply]
      rw [IsLocalizedModule.linearEquiv_apply]
      rw [IsLocalizedModule.linearEquiv_apply]
      exact LinearMap.baseChange_tmul f 1 x
  have hcomp' : g = eN.symm.toLinearMap ∘ₗ
      (f.baseChange K).restrictScalars R ∘ₗ eM.toLinearMap := by
    rw [← hcomp]
    simp
  have hgen : Function.Bijective g := by
    rw [hcomp']
    exact eN.symm.bijective.comp (hbij.comp eM.bijective)
  exact hgen

/-- A localized-module isomorphism induces an isomorphism after ordinary scalar extension to the
same localization. -/
theorem baseChange_bijective_of_localized_bijective
    (R : Type u) [CommRing R] (S : Submonoid R)
    (T : Type v) [CommRing T] [Algebra R T] [IsLocalization S T]
    (M : Type w) [AddCommGroup M] [Module R M]
    (N : Type z) [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hlocal : Function.Bijective
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N) f)) :
    Function.Bijective (f.baseChange T) := by
  let mM := LocalizedModule.mkLinearMap S M
  let mN := LocalizedModule.mkLinearMap S N
  let tM := TensorProduct.mk R T M 1
  let tN := TensorProduct.mk R T N 1
  let eM := IsLocalizedModule.linearEquiv S mM tM
  let eN := IsLocalizedModule.linearEquiv S mN tN
  let g := IsLocalizedModule.map S mM mN f
  have hcomp : eN.toLinearMap ∘ₗ g =
      (f.baseChange T).restrictScalars R ∘ₗ eM.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S mM tN
    exact LinearMap.ext fun x => by
      change eN (g (mM x)) = (f.baseChange T) (eM (mM x))
      rw [IsLocalizedModule.map_apply]
      rw [IsLocalizedModule.linearEquiv_apply]
      rw [IsLocalizedModule.linearEquiv_apply]
      exact LinearMap.baseChange_tmul f 1 x
  have hcomp' : (f.baseChange T).restrictScalars R =
      eN.toLinearMap ∘ₗ g ∘ₗ eM.symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := eM.surjective z
    simpa [LinearMap.comp_apply] using DFunLike.congr_fun hcomp x |>.symm
  have hres : Function.Bijective ((f.baseChange T).restrictScalars R) := by
    rw [hcomp']
    exact eN.bijective.comp (hlocal.comp eM.symm.bijective)
  exact hres

/-- A linear map that is bijective at the generic localization of a domain is bijective after
inverting one nonzero element. -/
theorem exists_nonzero_away_bijective_of_generic_localized_bijective
    (R : Type u) [CommRing R] [IsDomain R]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type z) [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N)
    (hgeneric : Function.Bijective
      (IsLocalizedModule.map (⊥ : Ideal R).primeCompl
        (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl M)
        (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl N) f)) :
    ∃ r : R, r ≠ 0 ∧ Function.Bijective
      (LocalizedModule.map (Submonoid.powers r) f) := by
  obtain ⟨r, hr, hbij⟩ := Module.FinitePresentation.exists_notMem_bijective f (⊥ : Ideal R)
    (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl M)
    (LocalizedModule.mkLinearMap (⊥ : Ideal R).primeCompl N) hgeneric
  exact ⟨r, by simpa using hr, hbij⟩

/-- A map between a finite module and a finitely presented module which becomes bijective over
the fraction field becomes bijective after inverting one nonzero element. -/
theorem exists_nonzero_away_bijective_of_fractionField_baseChange_bijective
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K]
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Type z) [AddCommGroup N] [Module R N] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) (hbij : Function.Bijective (f.baseChange K)) :
    ∃ r : R, r ≠ 0 ∧ Function.Bijective
      (LocalizedModule.map (Submonoid.powers r) f) := by
  exact exists_nonzero_away_bijective_of_generic_localized_bijective R M N f
    (generic_localized_bijective_of_fractionField_baseChange_bijective R K M N f hbij)

end GaloisForLFunctions.HTGeometry.ABHN
