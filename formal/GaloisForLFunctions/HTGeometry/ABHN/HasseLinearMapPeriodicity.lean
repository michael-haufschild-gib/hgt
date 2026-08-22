/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRelations

/-!
# Hasse detection of periodic linear maps

The equation `f ^ n = 1` is reflected by scalar extension.  Thus completed finite-order actions
certify the same global action.  The involution result is stated separately for constructions
whose natural specification is a function involutivity law.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- A fixed power of an endomorphism is the identity exactly when the same scalar-extended power
is the identity. -/
theorem linearMap_pow_eq_id_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (n : ℕ) :
    f ^ n = 1 ↔ (f.baseChange L) ^ n = 1 := by
  constructor
  · intro h
    calc
      (f.baseChange L) ^ n = (f ^ n).baseChange L := (LinearMap.baseChange_pow K L M f n).symm
      _ = (1 : Module.End K M).baseChange L := congrArg (LinearMap.baseChange L) h
      _ = 1 := LinearMap.baseChange_one K M
  · intro h
    apply (linearMap_eq_iff_baseChange_eq (L := L) (f ^ n) 1).mpr
    calc
      (f ^ n).baseChange L = (f.baseChange L) ^ n := LinearMap.baseChange_pow K L M f n
      _ = 1 := h
      _ = (1 : Module.End K M).baseChange L := (LinearMap.baseChange_one K M).symm

/-- An endomorphism is an involution exactly when its scalar extension is an involution. -/
theorem linearMap_involutive_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) : Function.Involutive f ↔ Function.Involutive (f.baseChange L) := by
  constructor
  · intro h
    have hf : f.comp f = LinearMap.id := by
      ext x
      exact h x
    have hbase : (f.baseChange L).comp (f.baseChange L) =
        (LinearMap.id : Module.End L (TensorProduct K L M)) := by
      rw [← LinearMap.baseChange_comp, hf, LinearMap.baseChange_id]
    intro x
    exact LinearMap.congr_fun hbase x
  · intro h
    have hbase : (f.baseChange L).comp (f.baseChange L) =
        (LinearMap.id : Module.End L (TensorProduct K L M)) := by
      apply LinearMap.ext
      intro x
      exact h x
    have hf : f.comp f = LinearMap.id :=
      (linearMap_eq_iff_baseChange_eq (L := L) (f.comp f) LinearMap.id).mpr (by
        simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_id] using hbase)
    intro x
    exact LinearMap.congr_fun hf x

/-- The `n`th power of an endomorphism over a number field is the identity exactly when this is
true after every completion. -/
theorem numberField_linearMap_pow_eq_id_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (n : ℕ) :
    f ^ n = 1 ↔ ∀ p : NumberFieldPlace K, (f.baseChange (completion K p)) ^ n = 1 := by
  constructor
  · intro h p
    exact (linearMap_pow_eq_id_iff_baseChange (L := completion K p) f n).mp h
  · intro h
    exact (linearMap_pow_eq_id_iff_baseChange (L := completion K (witnessPlace K)) f n).mpr
      (h (witnessPlace K))

/-- Involutivity of an endomorphism over a number field is detected at every completed place. -/
theorem numberField_linearMap_involutive_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    Function.Involutive f ↔ ∀ p : NumberFieldPlace K,
      Function.Involutive (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_involutive_iff_baseChange (L := completion K p) f).mp h
  · intro h
    exact (linearMap_involutive_iff_baseChange
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- The `n`th power of an endomorphism over `F(t)` is the identity exactly when this is true after
every finite and infinite completion. -/
theorem rationalFunction_linearMap_pow_eq_id_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (n : ℕ) :
    f ^ n = 1 ↔ ∀ p : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F p)) ^ n = 1 := by
  constructor
  · intro h p
    exact (linearMap_pow_eq_id_iff_baseChange
      (L := rationalFunctionCompletion F p) f n).mp h
  · intro h
    exact (linearMap_pow_eq_id_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) f n).mpr
      (h RationalFunctionPlace.infinite)

/-- Involutivity of an endomorphism over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_linearMap_involutive_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    Function.Involutive f ↔ ∀ p : RationalFunctionPlace F,
      Function.Involutive (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_involutive_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_involutive_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) f).mpr
      (h RationalFunctionPlace.infinite)

/-- A prescribed finite order of a number-field endomorphism can be certified at one completion. -/
theorem numberField_linearMap_pow_eq_id_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) (n : ℕ) :
    f ^ n = 1 ↔ ∃ p : NumberFieldPlace K, (f.baseChange (completion K p)) ^ n = 1 := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_pow_eq_id_iff_baseChange (L := completion K (witnessPlace K)) f n).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_pow_eq_id_iff_baseChange (L := completion K p) f n).mpr hp

/-- Involutivity of a number-field endomorphism can be certified at one completion. -/
theorem numberField_linearMap_involutive_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    Function.Involutive f ↔ ∃ p : NumberFieldPlace K,
      Function.Involutive (f.baseChange (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_involutive_iff_baseChange (L := completion K (witnessPlace K)) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_involutive_iff_baseChange (L := completion K p) f).mpr hp

/-- A prescribed finite order of an `F(t)`-endomorphism can be certified at one completion. -/
theorem rationalFunction_linearMap_pow_eq_id_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) (n : ℕ) :
    f ^ n = 1 ↔ ∃ p : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F p)) ^ n = 1 := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_pow_eq_id_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f n).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_pow_eq_id_iff_baseChange
      (L := rationalFunctionCompletion F p) f n).mpr hp

/-- Involutivity of an `F(t)`-endomorphism can be certified at one completion. -/
theorem rationalFunction_linearMap_involutive_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    Function.Involutive f ↔ ∃ p : RationalFunctionPlace F,
      Function.Involutive (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_involutive_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_involutive_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
