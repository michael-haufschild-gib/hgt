import GaloisForLFunctions.HTGeometry.FiniteCuspMacbeath
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Finite-cusp Macbeath criterion on a convex subset

Positive-definite Hermitian forms are open only inside their self-adjoint linear subspace, not in
the raw matrix space.  Macbeath's theorem does not need ambient openness: a convex subset of a
locally convex real topological vector space is locally path connected, while nonemptiness and
convexity give contractibility and connectedness.  This module records that corrected form of the
finite-cusp criterion.
-/

namespace GaloisForLFunctions.HTGeometry

open Pointwise

variable {G E ι : Type*} [Group G]
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- Finite-cusp Macbeath criterion for a nonempty convex subset of a locally convex space.

Unlike the open-domain version, this theorem correctly applies when the domain is a positive cone
cut out inside a proper self-adjoint linear subspace of the raw matrix ambient space. -/
theorem isFinitelyPresented_of_finiteCuspMacbeath_convexSubset
    (D : Set E) (hDconvex : Convex ℝ D) (hDne : D.Nonempty)
    [MulAction G D] [ContinuousConstSMul G D]
    (S : Finset ι) (V : ι → Set D)
    (hVopen : ∀ i ∈ S, IsOpen (V i))
    (hVne : ∃ i ∈ S, (V i).Nonempty)
    (hVconn : IsPreconnected (finiteCuspUnion S V))
    (hcover : ⋃ g : G, g • finiteCuspUnion S V = Set.univ)
    (hfinite : ∀ i ∈ S, ∀ j ∈ S,
      {g : G | ∃ x ∈ V i, g • x ∈ V j}.Finite) :
    IsFinitelyPresented G := by
  haveI := simplyConnectedSpace_of_convex hDconvex hDne
  haveI := hDconvex.locallyPathConnectedSpace E
  haveI := connectedSpace_of_convex hDconvex hDne
  exact isFinitelyPresented_of_macbeathHom_injective
    (isOpen_finiteCuspUnion S V hVopen)
    (finiteCuspUnion_nonempty S V hVne) hcover
    (meetSet_finiteCuspUnion_finite S V hfinite)
    (macbeathHom_injective
      (isOpen_finiteCuspUnion S V hVopen)
      (finiteCuspUnion_nonempty S V hVne) hVconn hcover)

end GaloisForLFunctions.HTGeometry
