import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingComposition
import GaloisForLFunctions.HTGeometry.DifferentialClockResolutionRigidity

/-!
# Strict conservative universality of differential clock embeddings

Finite differential clock frames compose strictly.  Hypertranscendental clock resolution is also
conservative under each embedding.  Closing these results under a two-step chain shows that an
irreversible sequence of differential field embeddings is simultaneously coherence-free and
incapable of relabelling the finite resolution index.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {F E L M : Type*} [Field F] [Field E] [Field L] [Field M]
  [Differential E] [Differential L] [Differential M]
  [Algebra F E] [Algebra F L] [Algebra F M]

/-- A composite differential embedding preserves and reflects the numerical clock resolution. -/
theorem jetObservableField_comp_map_eq_iff_resolution_eq
    (e : E →ₐ[F] L) (f : L →ₐ[F] M)
    (he : ∀ z : E, e z′ = (e z)′)
    (hf : ∀ z : L, f z′ = (f z)′)
    {x : E} (hx : HypertranscendentalOver F x) (P Q : ℕ) :
    (jetObservableField F x P).map (f.comp e) =
        jetObservableField F (f (e x)) Q ↔ P = Q := by
  exact jetObservableField_map_algHom_eq_iff_resolution_eq
    (f.comp e) (differentialAlgHom_comp_preserves_derivation e f he hf) hx P Q

/-- **Strict conservative differential-clock law.**  Along every two-step derivation-preserving
field embedding, finite clock-frame transport is literal composition and equality with a target
slice occurs exactly at the unchanged resolution. -/
theorem differentialClockEmbeddingChain_strictConservative
    (e : E →ₐ[F] L) (f : L →ₐ[F] M)
    (he : ∀ z : E, e z′ = (e z)′)
    (hf : ∀ z : L, f z′ = (f z)′)
    {x : E} (hx : HypertranscendentalOver F x) (P Q : ℕ) :
    ((jetObservableField F x P).map (f.comp e) =
        jetObservableField F (f (e x)) Q ↔ P = Q) ∧
      jetObservableFieldEmbeddingEquiv (f.comp e)
          (differentialAlgHom_comp_preserves_derivation e f he hf) x P =
        (jetObservableFieldEmbeddingEquiv e he x P).trans
          (jetObservableFieldEmbeddingEquiv f hf (e x) P) := by
  exact ⟨jetObservableField_comp_map_eq_iff_resolution_eq e f he hf hx P Q,
    jetObservableFieldEmbeddingEquiv_comp e f he hf x P⟩

end

end GaloisForLFunctions.HTGeometry
