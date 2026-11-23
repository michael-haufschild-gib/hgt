import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Finiteness.Basic

/-! A finite system of linear integrality conditions over a localization
can be cleared by one denominator. -/

noncomputable section

namespace GlobalTheory.PD

variable {A R F M : Type*} [CommRing A] [CommRing R] [CommRing F]
  [Algebra A R] [Algebra A F] [Algebra R F] [IsScalarTower A R F]
  [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Clear the denominators of a linear map from a finite module whose
image is contained in the localized base ring. -/
theorem exists_common_denominator (S : Submonoid A) [IsLocalization S R] (f : M →ₗ[A] F)
    (h : ∀ b, f b ∈ (algebraMap R F).range) :
    ∃ s : S, ∀ b, algebraMap A F (s : A) * f b ∈ (algebraMap A F).range := by
  classical
  let C := (algebraMap A F).range
  have hden (b : M) : ∃ s : S, algebraMap A F (s : A) * f b ∈ C := by
    obtain ⟨a, ha⟩ := h b
    obtain ⟨⟨c, s⟩, hc⟩ := IsLocalization.surj S a
    refine ⟨s, c, ?_⟩
    simpa only [map_mul, ha, ← IsScalarTower.algebraMap_apply A R F, mul_comm (f b)] using
      (congrArg (algebraMap R F) hc).symm
  have hfin (V : Finset M) : ∃ s : S, ∀ b ∈ V, algebraMap A F (s : A) * f b ∈ C := by
    induction V using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a V ha ih =>
      obtain ⟨s, hs⟩ := ih
      obtain ⟨t, ht⟩ := hden a
      refine ⟨s * t, fun b hb => ?_⟩
      change algebraMap A F ((s : A) * (t : A)) * f b ∈ C
      rcases Finset.mem_insert.mp hb with rfl | hb
      · rw [map_mul, mul_assoc]
        exact C.mul_mem ⟨s, rfl⟩ ht
      · rw [mul_comm (s : A), map_mul, mul_assoc]
        exact C.mul_mem ⟨t, rfl⟩ (hs b hb)
  obtain ⟨V, hV⟩ := Module.Finite.fg_top (R := A) (M := M)
  obtain ⟨s, hs⟩ := hfin V
  let N := (LinearMap.range (Algebra.linearMap A F)).comap ((s : A) • f)
  have hle : Submodule.span A (V : Set M) ≤ N := Submodule.span_le.mpr fun b hb => by
    change (s : A) • f b ∈ C
    rw [Algebra.smul_def]
    exact hs b hb
  refine ⟨s, fun b => ?_⟩
  change (algebraMap A F (s : A) * f b) ∈ C
  have hb : b ∈ N := hle (hV.symm ▸ Submodule.mem_top)
  change (s : A) • f b ∈ C at hb
  rwa [Algebra.smul_def] at hb

end GlobalTheory.PD
