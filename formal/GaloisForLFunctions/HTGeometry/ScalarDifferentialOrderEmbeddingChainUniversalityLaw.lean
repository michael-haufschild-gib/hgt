import GaloisForLFunctions.HTGeometry.ScalarDifferentialRationalOrder
import GaloisForLFunctions.HTGeometry.DifferentialClockEmbeddingComposition
import GaloisForLFunctions.HTGeometry.DifferentialClockResolutionRigidity

/-!
# Scalar differential order embedding-chain universality

Exact scalar differential order is functorial across derivation-preserving embeddings with a
different codomain, not only differential endomorphisms.  Along every two-step field-embedding
chain it is preserved together with the numerical clock resolution.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- A derivation-preserving field embedding into an arbitrary codomain preserves exact scalar
differential order. -/
theorem HasScalarDifferentialOrder.mapTo
    {C E L : Type*} [Field C] [Field E] [Field L]
    [Algebra C E] [Algebra C L] [Differential E] [Differential L]
    {y z : E} {n : ℕ} (e : E →ₐ[C] L)
    (hderiv : ∀ w : E, e w′ = (e w)′)
    (hz : HasScalarDifferentialOrder C y z n) :
    HasScalarDifferentialOrder C (e y) (e z) n := by
  constructor
  · rw [← jetObservableField_map_algHom e hderiv y (n + 1)]
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y (n + 1)) e (x := z)).mpr hz.1
  · intro hlow
    apply hz.2
    rw [← jetObservableField_map_algHom e hderiv y n] at hlow
    exact (IntermediateField.map_mem_map
      (S := jetObservableField C y n) e (x := z)).mp hlow

/-- **Scalar-order/clock-resolution embedding-chain law.**  A two-step differential embedding
preserves the exact order of every scalar observable and can identify a transported clock slice
with a target slice only at the unchanged resolution index. -/
theorem scalarDifferentialOrder_embeddingChain_preserved_and_resolutionRigid
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
          jetObservableField C (f (e y)) Q ↔ P = Q) := by
  have hcomp := differentialAlgHom_comp_preserves_derivation e f he hf
  exact ⟨hz.mapTo (f.comp e) hcomp,
    jetObservableField_map_algHom_eq_iff_resolution_eq (f.comp e) hcomp hy P Q⟩

end

end GaloisForLFunctions.HTGeometry
