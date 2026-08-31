import GaloisForLFunctions.HTGeometry.ParameterizedDifferenceGalois
import GaloisForLFunctions.HTGeometry.DifferentialDeltaSimple

/-!
# Reducedness of sigma-delta-simple rings

In characteristic zero the nilradical is stable under both a ring automorphism and a derivation.
It is therefore trivial in every nontrivial ring simple for the combined difference-differential
structure.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

variable {R : Type*} [CommRing R] [Nontrivial R] [Algebra ℚ R] [Differential R]

/-- Every nontrivial characteristic-zero `σ`-`δ`-simple ring is reduced. -/
theorem isReduced_of_isSigmaDeltaSimple {σ : R ≃+* R}
    (h : IsSigmaDeltaSimple σ) : IsReduced R := by
  have hnil : nilradical R = ⊥ := by
    rcases h _ ⟨isSigmaIdeal_nilradical σ, isDeltaIdeal_nilradical⟩ with hb | ht
    · exact hb
    · exfalso
      have h1 : (1 : R) ∈ nilradical R := by rw [ht]; trivial
      obtain ⟨n, hn⟩ := h1
      rw [one_pow] at hn
      exact one_ne_zero hn
  refine ⟨fun x hx => ?_⟩
  have hxn : x ∈ nilradical R := mem_nilradical.mpr hx
  rw [hnil] at hxn
  simpa using hxn

end GaloisForLFunctions.HTGeometry
