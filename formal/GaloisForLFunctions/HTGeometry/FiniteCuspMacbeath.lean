import GaloisForLFunctions.HTGeometry.MacbeathConvexDomain

/-!
# Macbeath's criterion for finitely many cusps

Arithmetic reduction over a number ring produces finitely many cusp neighbourhoods rather than
one principal cusp.  This module aggregates them without losing the finite-overlap conclusion:
pairwise finiteness of every cusp-transition set implies finiteness of the overlap set of the
whole finite union.  Macbeath's convex-domain criterion then applies to that union.
-/

namespace GaloisForLFunctions.HTGeometry

open Pointwise

variable {G X E ι : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [LocallyPathConnectedSpace E]

/-- Union of a finite family of cusp neighbourhoods. -/
def finiteCuspUnion (S : Finset ι) (V : ι → Set X) : Set X :=
  ⋃ i ∈ S, V i

theorem isOpen_finiteCuspUnion (S : Finset ι) (V : ι → Set X)
    (hV : ∀ i ∈ S, IsOpen (V i)) : IsOpen (finiteCuspUnion S V) := by
  classical
  exact isOpen_iUnion fun i => isOpen_iUnion fun hi => hV i hi

theorem finiteCuspUnion_nonempty (S : Finset ι) (V : ι → Set X)
    (hne : ∃ i ∈ S, (V i).Nonempty) : (finiteCuspUnion S V).Nonempty := by
  rcases hne with ⟨i, hi, x, hx⟩
  exact ⟨x, Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hx⟩⟩⟩

/-- Pairwise finiteness of transitions between finitely many cusp neighbourhoods implies
finiteness of the overlap set of their union. -/
theorem meetSet_finiteCuspUnion_finite (S : Finset ι) (V : ι → Set X)
    (hfinite : ∀ i ∈ S, ∀ j ∈ S,
      {g : G | ∃ x ∈ V i, g • x ∈ V j}.Finite) :
    (meetSet (G := G) (finiteCuspUnion S V)).Finite := by
  classical
  let T : Set G := ⋃ i ∈ S, ⋃ j ∈ S, {g : G | ∃ x ∈ V i, g • x ∈ V j}
  have hT : T.Finite := by
    dsimp [T]
    exact Set.Finite.biUnion (S.finite_toSet) fun i hi =>
      Set.Finite.biUnion (S.finite_toSet) fun j hj => hfinite i hi j hj
  refine hT.subset ?_
  rintro g ⟨x, hxg, hx⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hxg
  rcases Set.mem_iUnion.1 hxg with ⟨i, hi⟩
  rcases Set.mem_iUnion.1 hi with ⟨hiS, hxi⟩
  rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
  rcases Set.mem_iUnion.1 hj with ⟨hjS, hxj⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hiS, ?_⟩⟩
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hjS, ?_⟩⟩
  exact ⟨g⁻¹ • x, hxi, by simpa using hxj⟩

/-- Finite-cusp Macbeath criterion on an open convex domain.  The covering set is a finite union;
only pairwise cusp-transition finiteness must be checked. -/
theorem isFinitelyPresented_of_finiteCuspMacbeath_convex
    (D : Set E) (hDopen : IsOpen D) (hDconvex : Convex ℝ D) (hDne : D.Nonempty)
    [MulAction G D] [ContinuousConstSMul G D]
    (S : Finset ι) (V : ι → Set D)
    (hVopen : ∀ i ∈ S, IsOpen (V i))
    (hVne : ∃ i ∈ S, (V i).Nonempty)
    (hVconn : IsPreconnected (finiteCuspUnion S V))
    (hcover : ⋃ g : G, g • finiteCuspUnion S V = Set.univ)
    (hfinite : ∀ i ∈ S, ∀ j ∈ S,
      {g : G | ∃ x ∈ V i, g • x ∈ V j}.Finite) :
    IsFinitelyPresented G := by
  exact isFinitelyPresented_of_macbeath_convex hDopen hDconvex hDne
    (isOpen_finiteCuspUnion S V hVopen)
    (finiteCuspUnion_nonempty S V hVne) hVconn hcover
    (meetSet_finiteCuspUnion_finite S V hfinite)

end GaloisForLFunctions.HTGeometry
