import GaloisForLFunctions.HTGeometry.SubsystemComponentWitness

/-!
# Temporal curvature of a pair of sites

Equation `(5)` computes the temporal rank read by a vertex subset as a sum over
the connected components of the induced graph.  That sum is exactly the
combinatorial component-factorized rank already studied for finite graphs, so
the pair curvature

```
κ(u,v) = τ({u,v}) − τ({u}) − τ({v})
```

of an actual generic Hamiltonian obeys the exact interaction law: it is
`(q_u − 1)(q_v − 1)` across an interaction edge and zero otherwise, and its
positivity reconstructs adjacency.
-/

open scoped Matrix BigOperators
open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Component packets are exactly the images of the connected-component
supports. -/
theorem componentPackets_eq_image (G : SimpleGraph V) (S : Finset V) :
    componentPackets G S =
      Finset.univ.image
        (fun C : (inducedSubsystemGraph G S).ConnectedComponent =>
          subsystemPacketImage C.supp.toFinite.toFinset) := by
  ext P
  constructor
  · intro hP
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hP
    exact Finset.mem_image.2
      ⟨(inducedSubsystemGraph G S).connectedComponentMk v,
        Finset.mem_univ _, hv⟩
  · intro hP
    obtain ⟨C, -, hC⟩ := Finset.mem_image.1 hP
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ v =>
        exact Finset.mem_image.2
          ⟨v, Finset.mem_attach _ _, hC⟩

/-- **The generic subsystem rank is the combinatorial component rank.** -/
theorem sum_componentPackets_eq_finiteInducedGraphTemporalRank
    (G : SimpleGraph V) (S : Finset V) (q : V → ℕ) :
    ∑ c ∈ componentPackets G S, ((∏ v ∈ c, q v) - 1) =
      finiteInducedGraphTemporalRank G q S := by
  classical
  rw [componentPackets_eq_image]
  rw [Finset.sum_image]
  · unfold finiteInducedGraphTemporalRank finiteGraphTemporalRank
      finiteGraphComponentDimension
    refine Finset.sum_congr rfl fun C _ => ?_
    congr 1
    exact Finset.prod_image fun x _ y _ h => Subtype.val_injective h
  · intro C _ D _ hCD
    have hsupp : C.supp.toFinite.toFinset = D.supp.toFinite.toFinset := by
      refine Finset.image_injective Subtype.val_injective ?_
      exact hCD
    rw [← SimpleGraph.ConnectedComponent.supp_inj]
    ext w
    rw [← Set.Finite.mem_toFinset C.supp.toFinite,
      ← Set.Finite.mem_toFinset D.supp.toFinite, hsupp]

variable (A : V → Type*) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- **The generic temporal rank of a subsystem is the prescribed
component-factorized rank.** -/
theorem anchoredTemporalRank_eq_finiteInducedGraphTemporalRank
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ allSubsystemGenericSet A G) (S : Finset V) (r : ∀ v, A v) :
    anchoredTemporalRank
        (subsystemHamiltonian_isHermitian A G S p).eigenvalues r =
      finiteInducedGraphTemporalRank G (fun v => Fintype.card (A v)) S := by
  rw [anchoredTemporalRank_subsystemHamiltonian_of_generic A G hp S r]
  exact sum_componentPackets_eq_finiteInducedGraphTemporalRank G S _

/-- **Equations `(6)`–`(7)`: the pair temporal-curvature law.**  For a generic
interaction parameter, the temporal curvature of a pair of distinct sites is
`(q_u − 1)(q_v − 1)` across an interaction edge and zero otherwise. -/
theorem pairTemporalCurvature_eq
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ allSubsystemGenericSet A G) (r : ∀ v, A v)
    {u v : V} (huv : u ≠ v) :
    anchoredTemporalRank
          (subsystemHamiltonian_isHermitian A G {u, v} p).eigenvalues r -
        anchoredTemporalRank
          (subsystemHamiltonian_isHermitian A G {u} p).eigenvalues r -
        anchoredTemporalRank
          (subsystemHamiltonian_isHermitian A G {v} p).eigenvalues r =
      if G.Adj u v then
        (Fintype.card (A u) - 1) * (Fintype.card (A v) - 1)
      else 0 := by
  rw [anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r,
    anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r,
    anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r]
  exact finiteGraphPairTemporalCurvature_eq G (fun v => Fintype.card (A v))
    (fun w => Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero) huv

/-- **Equation `(8)`: temporal curvature reconstructs the interaction graph.**
For a generic interaction parameter and local dimensions at least two, two
distinct sites interact exactly when their temporal curvature is positive. -/
theorem adj_iff_pairTemporalCurvature_pos
    {V : Type} [Fintype V] [DecidableEq V]
    (A : V → Type) [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]
    [∀ v, Nonempty (A v)]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h2 : ∀ v, 2 ≤ Fintype.card (A v))
    {p : Fin (interactionCoordinateCount A G) → ℝ}
    (hp : p ∈ allSubsystemGenericSet A G) (r : ∀ v, A v)
    {u v : V} (huv : u ≠ v) :
    G.Adj u v ↔
      0 < anchoredTemporalRank
            (subsystemHamiltonian_isHermitian A G {u, v} p).eigenvalues r -
          anchoredTemporalRank
            (subsystemHamiltonian_isHermitian A G {u} p).eigenvalues r -
          anchoredTemporalRank
            (subsystemHamiltonian_isHermitian A G {v} p).eigenvalues r := by
  rw [anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r,
    anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r,
    anchoredTemporalRank_eq_finiteInducedGraphTemporalRank A G hp _ r]
  exact adj_iff_finiteGraphPairTemporalCurvature_pos G
    (fun v => Fintype.card (A v)) h2 huv

end

end GaloisForLFunctions.HTGeometry
