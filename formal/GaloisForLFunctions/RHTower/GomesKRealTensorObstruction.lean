import GaloisForLFunctions.HTGeometry.GomesTensorConjugation
import GaloisForLFunctions.RHTower.KRealTensorProduct

/-!
# Partial Real structures do not descend through complex scalar extension

Applying the mixed-conjugation obstruction of Gomes, arXiv:2509.25276v7,
to the corpus's even `KRealStructure` shows why scalar and matter factors
must transform together. Fixing the scalar factor while transforming the
matter factor is possible exactly for the zero module. This contrasts with
the existing simultaneous tensor Real structure, which is well-defined.
-/

open scoped TensorProduct
namespace GaloisForLFunctions.RHTower

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A partial even Real action descends exactly when the entire matter module vanishes. -/
theorem kReal_partial_tensor_descent_iff (K : KRealStructure false M) :
    (∃ F : (ℂ ⊗[ℂ] M) → M,
      ∀ (z : ℂ) (m : M), F (z ⊗ₜ[ℂ] m) = z • K.sigma m) ↔
      ∀ m : M, m = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    have hz : (LinearMap.id : M →ₗ[ℂ] M) = 0 := by
      apply (HTGeometry.mixedConjugation_descent_iff LinearMap.id).mp
      refine ⟨fun x => K.sigma (F x), ?_⟩
      intro z m
      simp [hF, K.sq, kRealParityAction]
    intro m
    simpa using LinearMap.congr_fun hz m
  · intro hM
    exact ⟨fun _ => 0, fun z m => (hM _).symm⟩

end GaloisForLFunctions.RHTower
