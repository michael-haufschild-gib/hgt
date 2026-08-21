/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality

/-!
# Hasse detection of endomorphism relations

Scalar extension reflects the multiplication relations between fixed endomorphisms.  In
particular, commutation and idempotence are detected at every completion of the supported global
fields.  These certify a global multi-operator action and a global direct-sum projector from their
completed scalar extensions.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Two endomorphisms commute exactly when their scalar extensions commute. -/
theorem linearMap_commute_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f g : M →ₗ[K] M) :
    Commute f g ↔ Commute (f.baseChange L) (g.baseChange L) := by
  constructor
  · intro h
    change f.comp g = g.comp f at h
    change (f.baseChange L).comp (g.baseChange L) = (g.baseChange L).comp (f.baseChange L)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]
  · intro h
    change (f.baseChange L).comp (g.baseChange L) = (g.baseChange L).comp (f.baseChange L) at h
    change f.comp g = g.comp f
    exact (linearMap_eq_iff_baseChange_eq (L := L) (f.comp g) (g.comp f)).mpr (by
      simpa only [LinearMap.baseChange_comp] using h)

/-- An endomorphism is idempotent exactly when its scalar extension is idempotent. -/
theorem linearMap_isIdempotentElem_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) : IsIdempotentElem f ↔ IsIdempotentElem (f.baseChange L) := by
  constructor
  · intro h
    change f.comp f = f at h
    change (f.baseChange L).comp (f.baseChange L) = f.baseChange L
    rw [← LinearMap.baseChange_comp, h]
  · intro h
    change (f.baseChange L).comp (f.baseChange L) = f.baseChange L at h
    change f.comp f = f
    apply (linearMap_eq_iff_baseChange_eq (L := L) (f.comp f) f).mpr
    simpa only [LinearMap.baseChange_comp] using h

/-- A semiconjugacy relation between endomorphisms is reflected by field scalar extension. -/
theorem linearMap_semiconjBy_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f g h : M →ₗ[K] M) :
    SemiconjBy f g h ↔ SemiconjBy (f.baseChange L) (g.baseChange L) (h.baseChange L) := by
  constructor
  · intro hfg
    change f.comp g = h.comp f at hfg
    change (f.baseChange L).comp (g.baseChange L) = (h.baseChange L).comp (f.baseChange L)
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hfg]
  · intro hfg
    change (f.baseChange L).comp (g.baseChange L) = (h.baseChange L).comp (f.baseChange L) at hfg
    change f.comp g = h.comp f
    exact (linearMap_eq_iff_baseChange_eq (L := L) (f.comp g) (h.comp f)).mpr (by
      simpa only [LinearMap.baseChange_comp] using hfg)

/-- Commutation of endomorphisms over a number field is detected at every completed place. -/
theorem numberField_linearMap_commute_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f g : M →ₗ[K] M) :
    Commute f g ↔ ∀ p : NumberFieldPlace K,
      Commute (f.baseChange (completion K p)) (g.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_commute_iff_baseChange (L := completion K p) f g).mp h
  · intro h
    exact (linearMap_commute_iff_baseChange (L := completion K (witnessPlace K)) f g).mpr
      (h (witnessPlace K))

/-- Idempotence of an endomorphism over a number field is detected at every completed place. -/
theorem numberField_linearMap_isIdempotentElem_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    IsIdempotentElem f ↔ ∀ p : NumberFieldPlace K,
      IsIdempotentElem (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_isIdempotentElem_iff_baseChange (L := completion K p) f).mp h
  · intro h
    exact (linearMap_isIdempotentElem_iff_baseChange
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- Commutation of endomorphisms over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_linearMap_commute_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f g : M →ₗ[RatFunc F] M) :
    Commute f g ↔ ∀ p : RationalFunctionPlace F,
      Commute (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_commute_iff_baseChange (L := rationalFunctionCompletion F p) f g).mp h
  · intro h
    exact (linearMap_commute_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) f g).mpr
      (h RationalFunctionPlace.infinite)

/-- Idempotence of an endomorphism over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_linearMap_isIdempotentElem_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    IsIdempotentElem f ↔ ∀ p : RationalFunctionPlace F,
      IsIdempotentElem (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_isIdempotentElem_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_isIdempotentElem_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) f).mpr
      (h RationalFunctionPlace.infinite)

/-- Semiconjugacy of endomorphisms over a number field is detected at every completed place. -/
theorem numberField_linearMap_semiconjBy_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f g h : M →ₗ[K] M) :
    SemiconjBy f g h ↔ ∀ p : NumberFieldPlace K,
      SemiconjBy (f.baseChange (completion K p)) (g.baseChange (completion K p))
        (h.baseChange (completion K p)) := by
  constructor
  · intro hfg p
    exact (linearMap_semiconjBy_iff_baseChange (L := completion K p) f g h).mp hfg
  · intro hfg
    exact (linearMap_semiconjBy_iff_baseChange
      (L := completion K (witnessPlace K)) f g h).mpr (hfg (witnessPlace K))

/-- Semiconjugacy of endomorphisms over `F(t)` is detected at every finite and infinite
completed place. -/
theorem rationalFunction_linearMap_semiconjBy_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f g h : M →ₗ[RatFunc F] M) :
    SemiconjBy f g h ↔ ∀ p : RationalFunctionPlace F,
      SemiconjBy (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p))
        (h.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro hfg p
    exact (linearMap_semiconjBy_iff_baseChange
      (L := rationalFunctionCompletion F p) f g h).mp hfg
  · intro hfg
    exact (linearMap_semiconjBy_iff_baseChange
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) f g h).mpr
      (hfg RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
