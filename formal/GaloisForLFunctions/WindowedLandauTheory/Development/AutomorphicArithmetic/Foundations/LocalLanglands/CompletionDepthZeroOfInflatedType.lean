import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompletionDepthZeroClass
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps

/-! Any nonzero inflated type map supplies a vector fixed by
first principal congruence in the completion. -/

noncomputable section

open NumberField IsDedekindDomain Matrix Representation
open GlobalTheory.GLq GlobalTheory.PRep

namespace GlobalTheory.GLp

variable {E : Type} [Field E] [NumberField E] {p n : ℕ} [Fact p.Prime]
  (v : HeightOneSpectrum (𝓞 E)) (i : ℚ_[p] ≃+* v.adicCompletion E) (hi : Continuous i)

include hi in
theorem depthZero_of_inflated_type (σ : IrrRep (GL (Fin n) (v.adicCompletion E)))
    (τ : FDRep ℂ (Gn p n))
    (ht : HasInflatedType (σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)) τ) :
    (show IrrGL (v.adicCompletion E) from ⟨n, σ.cl⟩).DepthZero v := by
  rw [IrrGL.depthZero_mk_iff, ← principalFixed_comp_eq_completionFixed v i hi]
  obtain ⟨j, hj₀, hj⟩ := ht
  have hnz : ∃ w, j w ≠ 0 := by
    by_contra! h
    exact hj₀ (LinearMap.ext h)
  obtain ⟨w, hw⟩ := hnz
  let r := σ.ρ.comp (GeneralLinearGroup.map i.toRingHom)
  refine (Submodule.ne_bot_iff _).mpr ⟨j w, (mem_principalFixed_iff r (j w)).mpr ?_, hw⟩
  intro z hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hk' : integralReduction p (Fin n) k = 1 := hk
  simpa only [hk', map_one, Module.End.one_apply] using (hj k w).symm

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.depthZero_of_inflated_type
