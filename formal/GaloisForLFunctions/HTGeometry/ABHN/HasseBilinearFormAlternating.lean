/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality

/-!
# Hasse certification of alternating and reflexive bilinear forms

Alternation is invariant under field scalar extension. Consequently, it can be detected at every
completion, and it holds globally exactly when it holds locally everywhere. Reflexivity descends
through field scalar extension, so local reflexivity still certifies the global property.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Alternation of a bilinear form descends through field scalar extension. -/
theorem bilinForm_isAlt_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : (B.baseChange L).IsAlt) : B.IsAlt := by
  intro x
  apply FaithfulSMul.algebraMap_injective K L
  simpa [Algebra.smul_def] using h (1 ⊗ₜ[K] x)

/-- Alternation of a bilinear form is preserved by field scalar extension. -/
theorem bilinForm_isAlt_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : B.IsAlt) : (B.baseChange L).IsAlt := by
  have hskew : ∀ x y : L ⊗[K] M,
      B.baseChange L x y + B.baseChange L y x = 0 := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz =>
      calc
        B.baseChange L (x + z) y + B.baseChange L y (x + z) =
            (B.baseChange L x y + B.baseChange L z y) +
              (B.baseChange L y x + B.baseChange L y z) := by
                simp only [map_add, LinearMap.add_apply]
        _ = (B.baseChange L x y + B.baseChange L y x) +
              (B.baseChange L z y + B.baseChange L y z) := by ac_rfl
        _ = 0 := by rw [hx, hz, add_zero]
    | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz =>
        calc
          B.baseChange L (a ⊗ₜ[K] x) (y + z) +
              B.baseChange L (y + z) (a ⊗ₜ[K] x) =
              (B.baseChange L (a ⊗ₜ[K] x) y + B.baseChange L (a ⊗ₜ[K] x) z) +
                (B.baseChange L y (a ⊗ₜ[K] x) + B.baseChange L z (a ⊗ₜ[K] x)) := by
                  simp only [map_add, LinearMap.add_apply]
          _ = (B.baseChange L (a ⊗ₜ[K] x) y + B.baseChange L y (a ⊗ₜ[K] x)) +
                (B.baseChange L (a ⊗ₜ[K] x) z + B.baseChange L z (a ⊗ₜ[K] x)) := by ac_rfl
          _ = 0 := by rw [hy, hz, add_zero]
      | tmul b y =>
        rw [LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul, ← h.neg_eq x y, mul_comm b a,
          neg_smul, add_neg_cancel]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    calc
      B.baseChange L (x + y) (x + y) =
          (B.baseChange L x x + B.baseChange L x y) +
            (B.baseChange L y x + B.baseChange L y y) := by
              simp only [map_add, LinearMap.add_apply]
              ac_rfl
      _ = (B.baseChange L x x + B.baseChange L y y) +
            (B.baseChange L x y + B.baseChange L y x) := by ac_rfl
      _ = 0 := by rw [hx, hy, hskew, add_zero, zero_add]
  | tmul a x => simp [LinearMap.BilinForm.baseChange_tmul, h.self_eq_zero x]

/-- Alternation of a bilinear form is detected by field scalar extension. -/
theorem bilinForm_isAlt_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) : B.IsAlt ↔ (B.baseChange L).IsAlt := by
  constructor
  · exact bilinForm_isAlt_baseChange B
  · exact bilinForm_isAlt_of_baseChange B

/-- Reflexivity of a bilinear form descends through field scalar extension. -/
theorem bilinForm_isRefl_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : (B.baseChange L).IsRefl) : B.IsRefl := by
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective K L
  have hlocal := h (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) (by
    simp [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, hxy])
  simpa [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def] using hlocal

/-- Alternation of a bilinear form over a number field follows from alternation at every completed
place. -/
theorem numberField_bilinForm_isAlt_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsAlt) : B.IsAlt := by
  exact bilinForm_isAlt_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Alternation of a bilinear form over a number field is detected at every completed place. -/
theorem numberField_bilinForm_isAlt_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) :
    B.IsAlt ↔ ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsAlt := by
  constructor
  · intro h p
    exact (bilinForm_isAlt_iff_baseChange (L := completion K p) B).mp h
  · intro h
    exact (bilinForm_isAlt_iff_baseChange (L := completion K (witnessPlace K)) B).mpr
      (h (witnessPlace K))

/-- Reflexivity of a bilinear form over a number field follows from reflexivity at every completed
place. -/
theorem numberField_bilinForm_isRefl_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsRefl) : B.IsRefl := by
  exact bilinForm_isRefl_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Alternation of a bilinear form over `F(t)` follows from alternation at every finite and
infinite completed place. -/
theorem rationalFunction_bilinForm_isAlt_of_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsAlt) : B.IsAlt := by
  exact bilinForm_isAlt_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B
    (h RationalFunctionPlace.infinite)

/-- Alternation of a bilinear form over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_bilinForm_isAlt_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :
    B.IsAlt ↔ ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsAlt := by
  constructor
  · intro h p
    exact (bilinForm_isAlt_iff_baseChange
      (L := rationalFunctionCompletion F p) B).mp h
  · intro h
    exact (bilinForm_isAlt_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) B).mpr (h .infinite)

/-- Reflexivity of a bilinear form over `F(t)` follows from reflexivity at every finite and
infinite completed place. -/
theorem rationalFunction_bilinForm_isRefl_of_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsRefl) : B.IsRefl := by
  exact bilinForm_isRefl_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B
    (h RationalFunctionPlace.infinite)

/-- Alternation of a fixed bilinear form over a number field is certified at any one completed
place. -/
theorem numberField_bilinForm_isAlt_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) :
    B.IsAlt ↔ ∃ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsAlt := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (bilinForm_isAlt_iff_baseChange (L := completion K (witnessPlace K)) B).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_isAlt_iff_baseChange (L := completion K p) B).mpr hp

/-- Alternation of a fixed bilinear form over `F(t)` is certified at any one completed place. -/
theorem rationalFunction_bilinForm_isAlt_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :
    B.IsAlt ↔ ∃ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsAlt := by
  constructor
  · intro h
    exact ⟨.infinite,
      (bilinForm_isAlt_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) B).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_isAlt_iff_baseChange (L := rationalFunctionCompletion F p) B).mpr hp

/-- Reflexivity of a fixed number-field bilinear form descends from any one completed place. -/
theorem numberField_bilinForm_isRefl_of_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∃ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsRefl) : B.IsRefl := by
  obtain ⟨p, hp⟩ := h
  exact bilinForm_isRefl_of_baseChange (L := completion K p) B hp

/-- Reflexivity of a fixed `F(t)`-bilinear form descends from any one completed place. -/
theorem rationalFunction_bilinForm_isRefl_of_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∃ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsRefl) : B.IsRefl := by
  obtain ⟨p, hp⟩ := h
  exact bilinForm_isRefl_of_baseChange (L := rationalFunctionCompletion F p) B hp

end GaloisForLFunctions.HTGeometry.ABHN
