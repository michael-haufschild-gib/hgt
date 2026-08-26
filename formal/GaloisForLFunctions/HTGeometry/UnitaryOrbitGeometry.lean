import GaloisForLFunctions.HTGeometry.DenseFeatureGramUnitary

/-!
# Closed orbit geometry under a commuting unitary

A unitary which commutes with a marked operator family transports its marked closed cyclic
subspace exactly.  Consequently it preserves closure membership, cyclicity, approximation
distance, every inner product, and every finite Gram determinant.
-/

open Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E P J ι : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Vectors in the marked pieces of an operator orbit. -/
def markedOperatorOrbit (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P) : Set E :=
  {x | ∃ j p, p ∈ A j ∧ x = T p (g j)}

/-- Closed complex span of the marked pieces of an operator orbit. -/
def markedCyclicSubspace (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P) :
    Submodule ℂ E :=
  (Submodule.span ℂ (markedOperatorOrbit T g A)).topologicalClosure

/-- A linear isometric equivalence maps a closed submodule onto the closure of its image. -/
theorem unitary_map_topologicalClosure (U : E ≃ₗᵢ[ℂ] E) (S : Submodule ℂ E) :
    Submodule.map U.toLinearEquiv.toLinearMap S.topologicalClosure =
      (Submodule.map U.toLinearEquiv.toLinearMap S).topologicalClosure := by
  apply SetLike.coe_injective
  change U '' closure (S : Set E) = closure (U '' (S : Set E))
  exact U.toHomeomorph.image_closure (S : Set E)

/-- Commutation identifies the unitary image of the original marked orbit with the orbit of the
transported generators. -/
theorem unitary_image_markedOperatorOrbit
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) :
    U '' markedOperatorOrbit T g A =
      markedOperatorOrbit T (fun j => U (g j)) A := by
  ext y
  constructor
  · rintro ⟨x, ⟨j, p, hp, rfl⟩, rfl⟩
    exact ⟨j, p, hp, hcomm p (g j)⟩
  · rintro ⟨j, p, hp, rfl⟩
    exact ⟨T p (g j), ⟨j, p, hp, rfl⟩, hcomm p (g j)⟩

/-- Exact transport of the marked closed cyclic subspace. -/
theorem unitary_map_markedCyclicSubspace
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) :
    Submodule.map U.toLinearEquiv.toLinearMap (markedCyclicSubspace T g A) =
      markedCyclicSubspace T (fun j => U (g j)) A := by
  unfold markedCyclicSubspace
  rw [unitary_map_topologicalClosure, Submodule.map_span]
  change (Submodule.span ℂ (U '' markedOperatorOrbit T g A)).topologicalClosure = _
  rw [unitary_image_markedOperatorOrbit U T g A hcomm]

/-- Set-level exact transport of the marked closed cyclic subspace. -/
theorem unitary_image_markedCyclicSubspace
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) :
    U '' (markedCyclicSubspace T g A : Set E) =
      (markedCyclicSubspace T (fun j => U (g j)) A : Set E) := by
  change (Submodule.map U.toLinearEquiv.toLinearMap (markedCyclicSubspace T g A) : Set E) = _
  rw [unitary_map_markedCyclicSubspace U T g A hcomm]

/-- Closure membership is invariant under simultaneous unitary transport. -/
theorem unitary_mem_markedCyclicSubspace_iff
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) (v : E) :
    U v ∈ markedCyclicSubspace T (fun j => U (g j)) A ↔
      v ∈ markedCyclicSubspace T g A := by
  have himage := unitary_image_markedCyclicSubspace U T g A hcomm
  constructor
  · intro hv
    have hv' : U v ∈ U '' (markedCyclicSubspace T g A : Set E) := by
      rw [himage]
      exact hv
    rcases hv' with ⟨x, hx, hUx⟩
    simpa [U.injective hUx] using hx
  · intro hv
    have hv' : U v ∈ U '' (markedCyclicSubspace T g A : Set E) := ⟨v, hv, rfl⟩
    rw [himage] at hv'
    exact hv'

/-- Distance to the marked closed cyclic subspace is invariant under simultaneous transport. -/
theorem unitary_infDist_markedCyclicSubspace
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) (v : E) :
    Metric.infDist (U v) (markedCyclicSubspace T (fun j => U (g j)) A : Set E) =
      Metric.infDist v (markedCyclicSubspace T g A : Set E) := by
  rw [← unitary_image_markedCyclicSubspace U T g A hcomm]
  exact Metric.infDist_image U.isometry

/-- Cyclicity is invariant under simultaneous unitary transport. -/
theorem unitary_markedCyclicSubspace_eq_top_iff
    (U : E ≃ₗᵢ[ℂ] E) (T : P → E →ₗ[ℂ] E) (g : J → E) (A : J → Set P)
    (hcomm : ∀ p x, U (T p x) = T p (U x)) :
    markedCyclicSubspace T (fun j => U (g j)) A = ⊤ ↔
      markedCyclicSubspace T g A = ⊤ := by
  constructor
  · intro htop
    apply top_unique
    intro v _
    exact (unitary_mem_markedCyclicSubspace_iff U T g A hcomm v).mp (by simp [htop])
  · intro htop
    rw [← unitary_map_markedCyclicSubspace U T g A hcomm, htop]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr U.surjective

/-- A unitary preserves the full Gram kernel of any vector family. -/
theorem unitary_gramMatrix (U : E ≃ₗᵢ[ℂ] E) (v : ι → E) :
    (fun i j => inner ℂ (U (v i)) (U (v j))) =
      fun i j => inner ℂ (v i) (v j) := by
  funext i j
  exact U.inner_map_map (v i) (v j)

/-- Hence every finite Gram determinant is unchanged. -/
theorem unitary_gramDeterminant [Fintype ι] [DecidableEq ι]
    (U : E ≃ₗᵢ[ℂ] E) (v : ι → E) :
    Matrix.det (fun i j => inner ℂ (U (v i)) (U (v j))) =
      Matrix.det (fun i j => inner ℂ (v i) (v j)) := by
  rw [unitary_gramMatrix U v]

end

end GaloisForLFunctions.HTGeometry
