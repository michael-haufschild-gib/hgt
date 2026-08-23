import GaloisForLFunctions.HTGeometry.CStarEnvelopeCommutative

/-!
# Hasse quotient at the Shilov boundary

Restriction to the Shilov boundary is surjective and loses exactly the Shilov ideal.  Hence
continuous functions modulo boundary-invisible functions are linearly equivalent to continuous
boundary data.  Equality and existence--uniqueness take the standard Hasse forms.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ShilovLocal

open Set ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The Shilov ideal regarded as a complex linear submodule. -/
noncomputable def shilovIdealLinearSubmodule
    (S : Submodule ℂ C(X, ℂ)) : Submodule ℂ C(X, ℂ) :=
  (shilovIdeal S).restrictScalars ℂ

omit [T2Space X] in
/-- The linear kernel of boundary restriction is exactly the Shilov ideal. -/
theorem envelopeMap_linearKer (S : Submodule ℂ C(X, ℂ)) :
    LinearMap.ker (envelopeMap S).toLinearMap = shilovIdealLinearSubmodule S := by
  ext f
  rw [LinearMap.mem_ker]
  change envelopeMap S f = 0 ↔ f ∈ shilovIdeal S
  exact envelopeMap_eq_zero_iff S f

/-- Continuous functions modulo the Shilov ideal are linearly equivalent to continuous functions
on the Shilov boundary. -/
noncomputable def shilovEnvelopeHasseQuotientEquiv
    (S : Submodule ℂ C(X, ℂ)) :
    (C(X, ℂ) ⧸ shilovIdealLinearSubmodule S) ≃ₗ[ℂ] C(shilovBoundary S, ℂ) :=
  (Submodule.quotEquivOfEq _ _ (envelopeMap_linearKer S).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (envelopeMap S).toLinearMap (envelopeMap_surjective S))

@[simp] theorem shilovEnvelopeHasseQuotientEquiv_mk
    (S : Submodule ℂ C(X, ℂ)) (f : C(X, ℂ)) :
    shilovEnvelopeHasseQuotientEquiv S (Submodule.Quotient.mk f) = envelopeMap S f := by
  rfl

omit [T2Space X] in
/-- Two continuous functions have the same Shilov-boundary values exactly when their difference is
in the Shilov ideal. -/
theorem shilovEnvelope_congr_hasse_iff
    (S : Submodule ℂ C(X, ℂ)) (f g : C(X, ℂ)) :
    f - g ∈ shilovIdealLinearSubmodule S ↔ envelopeMap S f = envelopeMap S g := by
  change f - g ∈ shilovIdeal S ↔ _
  rw [← envelopeMap_eq_zero_iff S, map_sub, sub_eq_zero]

/-- Every continuous boundary function has a global extension, unique modulo the Shilov ideal. -/
theorem shilovEnvelope_exists_unique_mod_ideal
    (S : Submodule ℂ C(X, ℂ)) (h : C(shilovBoundary S, ℂ)) :
    ∃ f : C(X, ℂ), envelopeMap S f = h ∧
      ∀ g : C(X, ℂ), envelopeMap S g = h ↔
        g - f ∈ shilovIdealLinearSubmodule S := by
  obtain ⟨f, hf⟩ := envelopeMap_surjective S h
  refine ⟨f, hf, fun g => ?_⟩
  simpa only [hf] using (shilovEnvelope_congr_hasse_iff S g f).symm

end ShilovLocal

end GaloisForLFunctions.HTGeometry
