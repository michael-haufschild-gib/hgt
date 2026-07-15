import GaloisForLFunctions.HTGeometry.DifferentialClockFiniteSlice

/-!
# Coherent composition of differential clock frames

Quantum reference-frame changes are useful only when successive changes compose coherently.  The
finite observable-field equivalences already constructed for a derivation-preserving field
embedding have this property exactly: identity embeddings induce identity observable frames, and
the frame induced by a composite embedding is the composite of the two induced frames.

Thus finite hypertranscendental clock slices form a strict functor under one-way differential field
embeddings.  No ambient inverse, path-coherence hypothesis, or temporal evolution is involved.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {F E L M : Type*} [Field F] [Field E] [Field L] [Field M]
  [Differential E] [Differential L] [Differential M]
  [Algebra F E] [Algebra F L] [Algebra F M]

/-- Derivation preservation is closed under composition of algebra embeddings. -/
theorem differentialAlgHom_comp_preserves_derivation
    (e : E →ₐ[F] L) (f : L →ₐ[F] M)
    (he : ∀ z : E, e z′ = (e z)′)
    (hf : ∀ z : L, f z′ = (f z)′) :
    ∀ z : E, (f.comp e) z′ = ((f.comp e) z)′ := by
  intro z
  change f (e z′) = (f (e z))′
  rw [he, hf]

/-- The identity algebra embedding preserves the derivation. -/
theorem differentialAlgHom_id_preserves_derivation :
    ∀ z : E, (AlgHom.id F E) z′ = ((AlgHom.id F E) z)′ := by
  intro z
  rfl

/-- The finite clock-frame equivalence induced by the identity embedding is the identity frame. -/
theorem jetObservableFieldEmbeddingEquiv_id (x : E) (N : ℕ) :
    jetObservableFieldEmbeddingEquiv (AlgHom.id F E)
        (differentialAlgHom_id_preserves_derivation (F := F) (E := E)) x N =
      AlgEquiv.refl := by
  ext z
  simp only [coe_jetObservableFieldEmbeddingEquiv_apply]
  rfl

/-- **Strict composition of finite differential clock frames.**  Restricting a composite
derivation-preserving embedding to a finite jet-observable field gives exactly the composite of
the two separately restricted equivalences.  Hence no independent coherence map is needed. -/
theorem jetObservableFieldEmbeddingEquiv_comp
    (e : E →ₐ[F] L) (f : L →ₐ[F] M)
    (he : ∀ z : E, e z′ = (e z)′)
    (hf : ∀ z : L, f z′ = (f z)′)
    (x : E) (N : ℕ) :
    jetObservableFieldEmbeddingEquiv (f.comp e)
        (differentialAlgHom_comp_preserves_derivation e f he hf) x N =
      (jetObservableFieldEmbeddingEquiv e he x N).trans
        (jetObservableFieldEmbeddingEquiv f hf (e x) N) := by
  ext z
  simp only [coe_jetObservableFieldEmbeddingEquiv_apply]
  rfl

/-- Pointwise form of strict frame composition for direct rewriting in clock consumers. -/
theorem jetObservableFieldEmbeddingEquiv_comp_apply
    (e : E →ₐ[F] L) (f : L →ₐ[F] M)
    (he : ∀ z : E, e z′ = (e z)′)
    (hf : ∀ z : L, f z′ = (f z)′)
    (x : E) (N : ℕ) (z : jetObservableField F x N) :
    jetObservableFieldEmbeddingEquiv (f.comp e)
        (differentialAlgHom_comp_preserves_derivation e f he hf) x N z =
      jetObservableFieldEmbeddingEquiv f hf (e x) N
        (jetObservableFieldEmbeddingEquiv e he x N z) := by
  have h := congrArg
    (fun g : jetObservableField F x N ≃ₐ[F]
        jetObservableField F (f (e x)) N => g z)
    (jetObservableFieldEmbeddingEquiv_comp e f he hf x N)
  exact h

end

end GaloisForLFunctions.HTGeometry
