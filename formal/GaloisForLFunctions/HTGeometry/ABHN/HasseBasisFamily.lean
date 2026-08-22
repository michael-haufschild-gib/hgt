/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSpanning
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearIndependence

/-!
# Hasse detection for fixed basis families

A fixed family is a basis precisely when it is linearly independent and spans.  Both conditions
are reflected by every field scalar extension, so a global basis family can be certified at all
completions.  This does not assert descent of independently chosen local bases.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- A fixed family is a basis after field scalar extension exactly when it was a basis before
scalar extension. -/
theorem basisFamily_one_tmul_iff {K : Type u} {L : Type v} {M : Type w} {ι : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] (b : ι → M) :
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤) ↔
      (LinearIndependent L (fun i ↦ (1 : L) ⊗ₜ[K] b i) ∧
        Submodule.span L (Set.range fun i ↦ (1 : L) ⊗ₜ[K] b i) = ⊤) := by
  constructor
  · rintro ⟨hli, hspan⟩
    exact ⟨(linearIndependent_one_tmul_iff (L := L) b).mp hli,
      (span_range_eq_top_iff_baseChange (L := L) b).mp hspan⟩
  · rintro ⟨hli, hspan⟩
    exact ⟨(linearIndependent_one_tmul_iff (L := L) b).mpr hli,
      (span_range_eq_top_iff_baseChange (L := L) b).mpr hspan⟩

/-- A fixed family over a number field is a basis exactly when its scalar extension is a basis
at every completed place. -/
theorem numberField_basisFamily_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module K M] (b : ι → M) :
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤) ↔
      ∀ p : NumberFieldPlace K,
        LinearIndependent (completion K p) (fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) ∧
          Submodule.span (completion K p)
            (Set.range fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) = ⊤ := by
  constructor
  · intro h p
    exact (basisFamily_one_tmul_iff (L := completion K p) b).mp h
  · intro h
    exact (basisFamily_one_tmul_iff (L := completion K (witnessPlace K)) b).mpr
      (h (witnessPlace K))

/-- A fixed family over `F(t)` is a basis exactly when its scalar extension is a basis at every
finite and infinite completed place. -/
theorem rationalFunction_basisFamily_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] (b : ι → M) :
    (LinearIndependent (RatFunc F) b ∧ Submodule.span (RatFunc F) (Set.range b) = ⊤) ↔
      ∀ p : RationalFunctionPlace F,
        LinearIndependent (rationalFunctionCompletion F p)
          (fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) ∧
          Submodule.span (rationalFunctionCompletion F p)
            (Set.range fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) = ⊤ := by
  constructor
  · intro h p
    exact (basisFamily_one_tmul_iff (L := rationalFunctionCompletion F p) b).mp h
  · intro h
    exact (basisFamily_one_tmul_iff (L := rationalFunctionCompletion F .infinite) b).mpr
      (h .infinite)

/-- A fixed basis family over a number field can be certified at one completion. -/
theorem numberField_basisFamily_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module K M] (b : ι → M) :
    (LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤) ↔
      ∃ p : NumberFieldPlace K,
        LinearIndependent (completion K p) (fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) ∧
          Submodule.span (completion K p)
            (Set.range fun i ↦ (1 : completion K p) ⊗ₜ[K] b i) = ⊤ := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (basisFamily_one_tmul_iff (L := completion K (witnessPlace K)) b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (basisFamily_one_tmul_iff (L := completion K p) b).mpr hp

/-- A fixed basis family over `F(t)` can be certified at one completion. -/
theorem rationalFunction_basisFamily_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {ι : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] (b : ι → M) :
    (LinearIndependent (RatFunc F) b ∧ Submodule.span (RatFunc F) (Set.range b) = ⊤) ↔
      ∃ p : RationalFunctionPlace F,
        LinearIndependent (rationalFunctionCompletion F p)
          (fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) ∧
          Submodule.span (rationalFunctionCompletion F p)
            (Set.range fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] b i) = ⊤ := by
  constructor
  · intro h
    exact ⟨.infinite,
      (basisFamily_one_tmul_iff (L := rationalFunctionCompletion F .infinite) b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (basisFamily_one_tmul_iff (L := rationalFunctionCompletion F p) b).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
