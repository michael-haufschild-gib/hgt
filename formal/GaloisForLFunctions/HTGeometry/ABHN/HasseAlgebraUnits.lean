import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Hasse detection of units in central simple algebras

For a finite-dimensional central simple algebra, invertibility of a fixed element is reflected by
any field scalar extension.  Consequently, it is detected at all completions of a number field or
of a rational function field.  This reflection uses finite-dimensional linear algebra and is not a
generic property of arbitrary injective ring maps.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Invertibility of an element of a finite-dimensional central simple algebra is reflected by
arbitrary field scalar extension. -/
theorem scalarExtensionMap_isUnit_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    IsUnit a ↔ IsUnit (scalarExtensionMap (L := L) A a) := by
  have hmul :
      LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) =
        (LinearMap.mulLeft K a).baseChange L := by
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul l x =>
      rw [LinearMap.baseChange_tmul]
      simp [scalarExtensionMap, Algebra.TensorProduct.tmul_mul_tmul]
  constructor
  · intro h
    exact h.map (scalarExtensionMap (L := L) A)
  · intro h
    apply IsUnit.isUnit_iff_mulLeft_bijective.mpr
    have hlocalLmulUnit : IsUnit (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)) := by
      change IsUnit ((Algebra.lmul L (L ⊗[K] A.carrier))
        (scalarExtensionMap (L := L) A a))
      exact Algebra.lmul_isUnit_iff.mpr h
    have hbaseBij : Function.Bijective ((LinearMap.mulLeft K a).baseChange L) := by
      rw [← hmul]
      exact (Module.End.isUnit_iff _).mp hlocalLmulUnit
    have hglobalInj : Function.Injective (LinearMap.mulLeft K a) := by
      intro x y hxy
      apply Algebra.TensorProduct.includeRight_injective
        (FaithfulSMul.algebraMap_injective K L)
      apply hbaseBij.1
      change (LinearMap.mulLeft K a).baseChange L (1 ⊗ₜ[K] x) =
        (LinearMap.mulLeft K a).baseChange L (1 ⊗ₜ[K] y)
      simpa only [LinearMap.baseChange_tmul, LinearMap.mulLeft_apply] using
        congrArg (fun z => (1 : L) ⊗ₜ[K] z) hxy
    exact ⟨hglobalInj, LinearMap.surjective_of_injective hglobalInj⟩

/-- An element of a central simple algebra over a number field is a unit exactly when it becomes
a unit at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_isUnit_iff_forall_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a : A.carrier) :
    IsUnit a ↔ ∀ p : NumberFieldPlace K,
      IsUnit (numberFieldLocalScalarExtensionMap K p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isUnit_iff (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isUnit_iff (L := completion K (witnessPlace K)) A a).mpr
      (h (witnessPlace K))

/-- An element of a central simple algebra over `F(t)` is a unit exactly when it becomes a unit
at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_isUnit_iff_forall_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    IsUnit a ↔ ∀ p : RationalFunctionPlace F,
      IsUnit (rationalFunctionLocalScalarExtensionMap F p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isUnit_iff (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isUnit_iff (L := rationalFunctionCompletion F .infinite) A a).mpr
      (h .infinite)

/-- Invertibility of a number-field CSA element is detected at one completion. -/
theorem numberFieldLocalScalarExtensionMap_isUnit_iff_exists_place
    (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) (a : A.carrier) :
    IsUnit a ↔ ∃ p : NumberFieldPlace K,
      IsUnit (numberFieldLocalScalarExtensionMap K p A a) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_isUnit_iff (L := completion K (witnessPlace K)) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_isUnit_iff (L := completion K p) A a).mpr hp

/-- Invertibility of a rational-function-field CSA element is detected at one finite or infinite
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_isUnit_iff_exists_place
    (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    IsUnit a ↔ ∃ p : RationalFunctionPlace F,
      IsUnit (rationalFunctionLocalScalarExtensionMap F p A a) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_isUnit_iff
        (L := rationalFunctionCompletion F .infinite) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_isUnit_iff
      (L := rationalFunctionCompletion F p) A a).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
