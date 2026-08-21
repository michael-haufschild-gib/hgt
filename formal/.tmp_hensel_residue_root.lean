import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel

attribute [local instance] Ideal.Quotient.field

universe u

theorem tmp_nonarchimedeanLocalField_hensel_lift_residue_root
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (a₀ : 𝒪[K] ⧸ 𝓂[K])
    (hroot : aeval a₀ f = 0)
    (hsimple : aeval a₀ f.derivative ≠ 0) :
    ∃ a : 𝒪[K], f.IsRoot a ∧ Ideal.Quotient.mk 𝓂[K] a = a₀ := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hroot' : Ideal.Quotient.mk 𝓂[K] (f.eval b) = 0 := by
    simpa only [aeval_def, eval₂_at_apply] using hroot
  have hsimple' : Ideal.Quotient.mk 𝓂[K] (f.derivative.eval b) ≠ 0 := by
    simpa only [aeval_def, eval₂_at_apply] using hsimple
  obtain ⟨a, ha, hab⟩ := nonarchimedeanLocalField_hensel_lift K f hf b hroot' hsimple'
  refine ⟨a, ha, ?_⟩
  exact Ideal.Quotient.eq.mpr hab

end GaloisForLFunctions.HTGeometry.ABHN
