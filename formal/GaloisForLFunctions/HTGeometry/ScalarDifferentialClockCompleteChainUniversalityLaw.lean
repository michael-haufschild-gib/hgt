import GaloisForLFunctions.HTGeometry.DifferentialClockStrictConservativeUniversalityLaw
import GaloisForLFunctions.HTGeometry.ScalarDifferentialOrderEmbeddingChainUniversalityLaw

/-!
# Complete scalar differential-clock embedding-chain universality

Exact scalar differential order, numerical clock resolution, and clock-frame composition are
three conservative aspects of one derivation-preserving embedding chain.  This module closes
the two terminal chain laws into one complete functorial statement.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- **Complete scalar differential-clock chain law.**  A two-step derivation-preserving field
embedding preserves exact scalar order, identifies transported and target jet fields exactly at
equal resolution, and transports clock frames by literal composition. -/
theorem scalarDifferentialClockEmbeddingChain_completeUniversality
    {C E L M : Type*} [Field C] [Field E] [Field L] [Field M]
    [Differential E] [Differential L] [Differential M]
    [Algebra C E] [Algebra C L] [Algebra C M]
    (e : E →ₐ[C] L) (f : L →ₐ[C] M)
    (he : ∀ w : E, e w′ = (e w)′)
    (hf : ∀ w : L, f w′ = (f w)′)
    {y z : E} {n : ℕ} (hy : HypertranscendentalOver C y)
    (hz : HasScalarDifferentialOrder C y z n) (P Q : ℕ) :
    HasScalarDifferentialOrder C (f (e y)) (f (e z)) n ∧
      ((jetObservableField C y P).map (f.comp e) =
          jetObservableField C (f (e y)) Q ↔ P = Q) ∧
      jetObservableFieldEmbeddingEquiv (f.comp e)
          (differentialAlgHom_comp_preserves_derivation e f he hf) y P =
        (jetObservableFieldEmbeddingEquiv e he y P).trans
          (jetObservableFieldEmbeddingEquiv f hf (e y) P) := by
  obtain ⟨horder, hresolution⟩ :=
    scalarDifferentialOrder_embeddingChain_preserved_and_resolutionRigid
      e f he hf hy hz P Q
  obtain ⟨_hresolution, hcomposition⟩ :=
    differentialClockEmbeddingChain_strictConservative e f he hf hy P Q
  exact ⟨horder, hresolution, hcomposition⟩

end

end GaloisForLFunctions.HTGeometry
