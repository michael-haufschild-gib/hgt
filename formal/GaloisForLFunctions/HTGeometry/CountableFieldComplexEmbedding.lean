import Mathlib

/-!
# Countable characteristic-zero fields embed into the complex numbers
-/

namespace GaloisForLFunctions.HTGeometry

open Cardinal Set

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-- A transcendence basis of `ℂ` over `ℚ` is infinite. -/
theorem infinite_of_isTranscendenceBasis_complex {t : Set ℂ}
    (ht : IsTranscendenceBasis ℚ ((↑) : t → ℂ)) : Infinite t := by
  rw [Set.infinite_coe_iff]
  intro hfin
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ℂ :=
    ht.isAlgebraic_field
  have hcard : Cardinal.mk (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) ≤ ℵ₀ := by
    refine le_trans (IntermediateField.cardinalMk_adjoin_le (F := ℚ) _) ?_
    have hs : Cardinal.mk (Set.range ((↑) : t → ℂ)) ≤ ℵ₀ := by
      rw [Subtype.range_coe_subtype, Set.setOf_mem_eq]
      exact (hfin.countable).le_aleph0
    have hq : Cardinal.mk ℚ ≤ ℵ₀ := Cardinal.mk_le_aleph0
    exact max_le (max_le hq hs) le_rfl
  haveI : Countable (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) :=
    Cardinal.mk_le_aleph0_iff.mp hcard
  have hall : (Set.univ : Set ℂ) =
      {z : ℂ | IsAlgebraic (IntermediateField.adjoin ℚ (Set.range ((↑) : t → ℂ))) z} := by
    ext z; simp [Algebra.IsAlgebraic.isAlgebraic z]
  have : (Set.univ : Set ℂ).Countable := by
    rw [hall]
    exact Algebraic.countable _ ℂ
  exact (Cardinal.not_countable_real) (this.preimage Complex.ofReal_injective)

/-- **`ℂ` carries a countably infinite algebraically independent family over `ℚ`.** -/
theorem exists_algebraicIndependent_nat_complex :
    ∃ z : ℕ → ℂ, AlgebraicIndependent ℚ z := by
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  haveI := infinite_of_isTranscendenceBasis_complex ht
  let e : ℕ ↪ t := Infinite.natEmbedding t
  exact ⟨fun n => ((e n : t) : ℂ), ht.1.comp e e.injective⟩

/-- **Every countable field of characteristic zero embeds into `ℂ`.** -/
theorem nonempty_ringHom_complex_of_countable
    (E : Type*) [Field E] [CharZero E] [Countable E] : Nonempty (E →+* ℂ) := by
  classical
  obtain ⟨b, hb⟩ := exists_isTranscendenceBasis ℚ E
  obtain ⟨z, hz⟩ := exists_algebraicIndependent_nat_complex
  obtain ⟨ι, hι⟩ : ∃ ι : b → ℕ, Function.Injective ι := Countable.exists_injective_nat b
  have hc : AlgebraicIndependent ℚ (fun i : b => z (ι i)) := hz.comp ι hι
  set A₁ := Algebra.adjoin ℚ (Set.range ((↑) : b → E)) with hA₁
  set A₂ := Algebra.adjoin ℚ (Set.range (fun i : b => z (ι i))) with hA₂
  let ψ : A₁ ≃ₐ[ℚ] A₂ := (hb.1.aevalEquiv.symm).trans hc.aevalEquiv
  letI : Algebra A₁ ℂ :=
    RingHom.toAlgebra ((algebraMap A₂ ℂ).comp (ψ : A₁ →+* A₂))
  have hinj : Function.Injective (algebraMap A₁ ℂ) := by
    have h1 : Function.Injective (ψ : A₁ →+* A₂) := ψ.injective
    have h2 : Function.Injective (algebraMap A₂ ℂ) := Subtype.val_injective
    exact h2.comp h1
  haveI : Module.IsTorsionFree A₁ ℂ := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r m hrm
    rw [Algebra.smul_def] at hrm
    rcases mul_eq_zero.mp hrm with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h
  haveI : Algebra.IsAlgebraic A₁ E := hb.isAlgebraic
  exact ⟨(IsAlgClosed.lift (R := A₁) (S := E) (M := ℂ) : E →ₐ[A₁] ℂ).toRingHom⟩

end GaloisForLFunctions.HTGeometry
