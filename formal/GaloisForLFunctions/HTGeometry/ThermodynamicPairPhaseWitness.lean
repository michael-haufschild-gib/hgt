import GaloisForLFunctions.HTGeometry.NestedPathEdgeDecomposition
import GaloisForLFunctions.HTGeometry.ThermodynamicPairPathHamiltonian
import GaloisForLFunctions.HTGeometry.ThermodynamicPathPhaseWitness

/-!
# Four-phase witness on the paired thermodynamic register

Transport the physical path-tree phase law through the adjacent-pair site equivalence.  This places
the exact diagonal tail witness on the same register and the same circuit-dependent cut used by the
two-qubit gate lower bound.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Weighted `P11` tree energy is invariant under an equivalence of physical sites. -/
theorem treePhaseEnergy_comap_equiv
    {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]
    (e : Q ≃ R) (P : SimpleGraph R)
    [Fintype P.edgeSet] [Fintype (P.comap e).edgeSet]
    (beta : Sym2 R → ℝ) (x : Config Q) :
    treePhaseEnergy (P.comap e) (fun E => beta (Sym2.map e E)) x =
      treePhaseEnergy P beta (fun r => x (e.symm r)) := by
  classical
  unfold treePhaseEnergy
  refine Finset.sum_bij (fun E _ => Sym2.map e E) ?_ ?_ ?_ ?_
  · intro E hE
    rw [SimpleGraph.mem_edgeFinset] at hE ⊢
    revert hE
    refine Sym2.inductionOn E ?_
    intro u v huv
    simp only [SimpleGraph.mem_edgeSet, Sym2.map_mk] at huv ⊢
    exact huv
  · intro E hE F hF hEq
    exact Sym2.map.injective e.injective hEq
  · intro F hF
    refine ⟨Sym2.map e.symm F, ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset] at hF ⊢
      revert hF
      refine Sym2.inductionOn F ?_
      intro u v huv
      simp only [SimpleGraph.mem_edgeSet, Sym2.map_mk] at huv ⊢
      simpa using huv
    · simp [Sym2.map_map]
  · intro E hE
    revert hE
    refine Sym2.inductionOn E ?_
    intro u v huv
    simp [edgeP11Value]

/-- Relabelling adjacent pairs by physical path order identifies the two path graphs exactly. -/
theorem thermodynamicPair_pathGraph_comap (N : ℕ) :
    (SimpleGraph.pathGraph ((N * 2 + 1) + 3)).comap
        (thermodynamicPairSiteEquiv N) =
      nestedQubitPathGraph (N + 2) := by
  ext u v
  simp only [SimpleGraph.comap_adj, nestedQubitPathGraph]
  simp only [SimpleGraph.pathGraph_adj]
  simp [thermodynamicPairSiteEquiv]

/-- Physical path graph expressed directly on the adjacent-pair circuit register. -/
def thermodynamicPairTailGraph (N : ℕ) : SimpleGraph (PairQubit (N + 2)) :=
  (SimpleGraph.pathGraph ((N * 2 + 1) + 3)).comap (thermodynamicPairSiteEquiv N)

/-- Pull the physical late-tail edge weight to the adjacent-pair circuit register. -/
def thermodynamicPairTailPhaseWeight (N K : ℕ)
    (E : Sym2 (PairQubit (N + 2))) : ℝ :=
  pathTailPhaseWeight (N * 2 + 1) K
    (Sym2.map (thermodynamicPairSiteEquiv N) E)

noncomputable local instance thermodynamicPhysicalPathEdgeSetFintype (N : ℕ) :
    Fintype (SimpleGraph.pathGraph ((N * 2 + 1) + 3)).edgeSet :=
  Fintype.ofFinite _

noncomputable local instance thermodynamicPairPathEdgeSetFintype (N : ℕ) :
    Fintype (thermodynamicPairTailGraph N).edgeSet :=
  Fintype.ofFinite _

/-- Pair-register tree phase equals the physical path-tree phase after configuration relabelling. -/
theorem treePhaseEnergy_thermodynamicPairTail_eq
    (N K : ℕ) (x : Config (PairQubit (N + 2))) :
    treePhaseEnergy (thermodynamicPairTailGraph N)
        (thermodynamicPairTailPhaseWeight N K) x =
      treePhaseEnergy (SimpleGraph.pathGraph ((N * 2 + 1) + 3))
        (pathTailPhaseWeight (N * 2 + 1) K)
        (qubitConfigurationEquiv (thermodynamicPairSiteEquiv N) x) := by
  letI : Fintype
      ((SimpleGraph.pathGraph ((N * 2 + 1) + 3)).comap
        (thermodynamicPairSiteEquiv N)).edgeSet := Fintype.ofFinite _
  exact treePhaseEnergy_comap_equiv (thermodynamicPairSiteEquiv N)
      (SimpleGraph.pathGraph ((N * 2 + 1) + 3))
      (pathTailPhaseWeight (N * 2 + 1) K) x

/-- Transport a cut and its sign orientation through a site equivalence. -/
theorem qubitConfigurationEquiv_cutFourConfig
    {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]
    (e : Q ≃ R) (A : Finset Q) (sigma : Q → Bool) (a b : Bool) :
    qubitConfigurationEquiv e (cutFourConfig A sigma a b) =
      cutFourConfig (A.map e.toEmbedding) (fun r => sigma (e.symm r)) a b := by
  funext r
  simp only [qubitConfigurationEquiv, Equiv.arrowCongr_apply]
  unfold cutFourConfig
  have hmem : r ∈ A.map e.toEmbedding ↔ e.symm r ∈ A := by
    constructor
    · intro hr
      obtain ⟨q, hq, heq⟩ := Finset.mem_map.mp hr
      simpa [← heq] using hq
    · intro hr
      exact Finset.mem_map.mpr ⟨e.symm r, hr, e.apply_symm_apply r⟩
  change orientedBit (sigma (e.symm r)) (if e.symm r ∈ A then a else b) =
    orientedBit (sigma (e.symm r)) (if r ∈ A.map e.toEmbedding then a else b)
  rw [if_congr hmem rfl rfl]

/-- Four-corner differencing of the paired tail-center energy is exactly its positive weighted path
cut. -/
theorem thermodynamicPairTailCenterEnergy_cut_mixed_eq_treePhaseEnergy
    (N K : ℕ) (A : Finset (PairQubit (N + 2)))
    (sigma : PairQubit (N + 2) → Bool) :
    thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false false) +
        thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true true) -
        thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false true) -
        thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true false) =
      treePhaseEnergy (thermodynamicPairTailGraph N)
          (thermodynamicPairTailPhaseWeight N K) (cutFourConfig A sigma false false) +
        treePhaseEnergy (thermodynamicPairTailGraph N)
          (thermodynamicPairTailPhaseWeight N K) (cutFourConfig A sigma true true) -
        treePhaseEnergy (thermodynamicPairTailGraph N)
          (thermodynamicPairTailPhaseWeight N K) (cutFourConfig A sigma false true) -
        treePhaseEnergy (thermodynamicPairTailGraph N)
          (thermodynamicPairTailPhaseWeight N K) (cutFourConfig A sigma true false) := by
  let e := thermodynamicPairSiteEquiv N
  let Aphysical := A.map e.toEmbedding
  let sigmaPhysical : Fin ((N * 2 + 1) + 3) → Bool := fun r => sigma (e.symm r)
  have hphysical := pathDiagEnergy_mobileTail_cut_mixed_eq_treePhaseEnergy
    (N * 2 + 1) K Aphysical sigmaPhysical
  have hconfig (a b : Bool) :
      cutFourConfig Aphysical sigmaPhysical a b =
        qubitConfigurationEquiv e (cutFourConfig A sigma a b) := by
    exact (qubitConfigurationEquiv_cutFourConfig e A sigma a b).symm
  rw [hconfig, hconfig, hconfig, hconfig] at hphysical
  rw [← treePhaseEnergy_thermodynamicPairTail_eq,
    ← treePhaseEnergy_thermodynamicPairTail_eq,
    ← treePhaseEnergy_thermodynamicPairTail_eq,
    ← treePhaseEnergy_thermodynamicPairTail_eq] at hphysical
  simpa [thermodynamicPairTailCenterEnergy, e, Aphysical, sigmaPhysical] using hphysical

/-- The pulled physical path remains a tree on the circuit register. -/
theorem thermodynamicPairTailGraph_isTree (N : ℕ) :
    (thermodynamicPairTailGraph N).IsTree := by
  exact (SimpleGraph.Iso.comap (thermodynamicPairSiteEquiv N)
    (SimpleGraph.pathGraph ((N * 2 + 1) + 3))).isTree_iff.mpr
      (SimpleGraph.pathGraph_isTree ((N * 2 + 1) + 2))

/-- Left physical edge index of a matching bond. -/
def thermodynamicMatchingPathEdgeIndex (N : ℕ) (j : Fin (N + 2)) :
    Fin ((N * 2 + 1) + 2) :=
  ⟨2 * j.val, by omega⟩

/-- Left physical edge index of an inter-pair bridge. -/
def thermodynamicBridgePathEdgeIndex (N : ℕ) (j : Fin ((N + 2) - 1)) :
    Fin ((N * 2 + 1) + 2) :=
  ⟨2 * j.val + 1, by omega⟩

theorem map_thermodynamicMatchingEdge (N : ℕ) (j : Fin (N + 2)) :
    Sym2.map (thermodynamicPairSiteEquiv N) (nestedMatchingEdge j) =
      pathEdgeSym ((N * 2 + 1) + 2) (thermodynamicMatchingPathEdgeIndex N j) := by
  unfold nestedMatchingEdge pathEdgeSym thermodynamicMatchingPathEdgeIndex
  simp only [Sym2.map_mk]
  apply Sym2.eq_iff.mpr
  left
  constructor <;> apply Fin.ext <;> simp

theorem map_thermodynamicBridgeEdge
    (N : ℕ) (j : Fin ((N + 2) - 1)) :
    Sym2.map (thermodynamicPairSiteEquiv N) (nestedBridgeEdge j) =
      pathEdgeSym ((N * 2 + 1) + 2) (thermodynamicBridgePathEdgeIndex N j) := by
  unfold nestedBridgeEdge pathEdgeSym thermodynamicBridgePathEdgeIndex
  simp only [Sym2.map_mk]
  apply Sym2.eq_iff.mpr
  left
  constructor <;> apply Fin.ext
  · simp [nestedBridgeLeft]
  · simp [nestedBridgeRight]
    omega

theorem nestedInfiniteEdgeWeight_even_index (j : ℕ) :
    nestedInfiniteEdgeWeight (2 * j) = 1 / (((j + 1 : ℕ) : ℝ) ^ 2) := by
  unfold nestedInfiniteEdgeWeight
  rw [if_pos (even_two_mul j)]
  congr 3
  omega

theorem nestedInfiniteEdgeWeight_odd_index (j : ℕ) :
    nestedInfiniteEdgeWeight (2 * j + 1) = 1 / (((j + 2 : ℕ) : ℝ) ^ 4) := by
  unfold nestedInfiniteEdgeWeight
  have hodd : ¬Even (2 * j + 1) := by simp
  rw [if_neg hodd]
  congr 3
  omega

@[simp] theorem thermodynamicPairTailPhaseWeight_matching
    (N K : ℕ) (j : Fin (N + 2)) :
    thermodynamicPairTailPhaseWeight N K (nestedMatchingEdge j) =
      if 4 * K ≤ 2 * j.val then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0 := by
  unfold thermodynamicPairTailPhaseWeight
  rw [map_thermodynamicMatchingEdge, pathTailPhaseWeight_pathEdge]
  simp only [thermodynamicMatchingPathEdgeIndex]
  by_cases htail : 4 * K ≤ 2 * j.val
  · rw [if_pos htail, nestedInfiniteEdgeWeight_even_index]
    simp [htail]
  · simp [htail]

@[simp] theorem thermodynamicPairTailPhaseWeight_bridge
    (N K : ℕ) (j : Fin ((N + 2) - 1)) :
    thermodynamicPairTailPhaseWeight N K (nestedBridgeEdge j) =
      if 4 * K ≤ 2 * j.val + 1 then 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) else 0 := by
  unfold thermodynamicPairTailPhaseWeight
  rw [map_thermodynamicBridgeEdge, pathTailPhaseWeight_pathEdge]
  simp only [thermodynamicBridgePathEdgeIndex]
  by_cases htail : 4 * K ≤ 2 * j.val + 1
  · rw [if_pos htail, nestedInfiniteEdgeWeight_odd_index]
    simp [htail]
  · simp [htail]

@[simp] theorem edgeCrosses_firstEndpointSites_matching_iff
    {L : ℕ} (S : Finset (Fin L)) (j : Fin L) :
    edgeCrosses (firstEndpointSites S) (nestedMatchingEdge j) = true ↔ j ∈ S := by
  rw [nestedMatchingEdge, edgeCrosses_mk]
  simp

@[simp] theorem edgeCrosses_firstEndpointSites_bridge_iff
    {L : ℕ} (S : Finset (Fin L)) (j : Fin (L - 1)) :
    edgeCrosses (firstEndpointSites S) (nestedBridgeEdge j) = true ↔
      nestedBridgeRight j ∈ S := by
  rw [nestedBridgeEdge, edgeCrosses_mk]
  simp [nestedBridgeLeft, nestedBridgeRight]

/-- Total positive tail weight crossing a circuit-selected cut. -/
def thermodynamicPairTailCrossingWeight
    (N K : ℕ) (A : Finset (PairQubit (N + 2))) : ℝ :=
  ∑ E ∈ (thermodynamicPairTailGraph N).edgeFinset.filter
      (fun E => edgeCrosses A E = true),
    |thermodynamicPairTailPhaseWeight N K E|

theorem thermodynamicPairTailGraph_edgeFinset_eq_union (N : ℕ) :
    (thermodynamicPairTailGraph N).edgeFinset =
      nestedMatchingEdges (N + 2) ∪ nestedBridgeEdges (N + 2) := by
  have hgraph : thermodynamicPairTailGraph N = nestedQubitPathGraph (N + 2) := by
    exact thermodynamicPair_pathGraph_comap N
  apply Finset.ext
  intro E
  rw [SimpleGraph.mem_edgeFinset, hgraph, ← SimpleGraph.mem_edgeFinset]
  rw [nestedPath_edgeFinset_eq_union (show 0 < N + 2 by omega)]

/-- Crossing weight decomposes into matching and bridge bonds on the paired path. -/
theorem thermodynamicPairTailCrossingWeight_firstEndpoint_expand
    (N K : ℕ) (S : Finset (Fin (N + 2))) :
    thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) =
      (∑ j : Fin (N + 2), if j ∈ S then
          |thermodynamicPairTailPhaseWeight N K (nestedMatchingEdge j)| else 0) +
        ∑ j : Fin ((N + 2) - 1), if nestedBridgeRight j ∈ S then
          |thermodynamicPairTailPhaseWeight N K (nestedBridgeEdge j)| else 0 := by
  classical
  unfold thermodynamicPairTailCrossingWeight
  rw [Finset.sum_filter, thermodynamicPairTailGraph_edgeFinset_eq_union,
    Finset.sum_union (nestedMatchingEdges_disjoint_bridgeEdges (N + 2))]
  congr 1
  · rw [nestedMatchingEdges, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hS : j ∈ S
      · simp [hS]
      · simp [hS]
    · exact fun _ _ _ _ h => nestedMatchingEdge_injective h
  · rw [nestedBridgeEdges, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      by_cases hS : nestedBridgeRight j ∈ S
      · simp [hS]
      · simp [hS]
    · exact fun _ _ _ _ h => nestedBridgeEdge_injective h

theorem sum_thermodynamicPairTail_matching_firstEndpoint
    {N K : ℕ} (hKL : 8 * K ≤ N + 2)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL) :
    (∑ j : Fin (N + 2), if j ∈ S then
        |thermodynamicPairTailPhaseWeight N K (nestedMatchingEdge j)| else 0) =
      ∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext j
    simp
  · intro j hj
    have hjS : j ∈ S := hj
    have hbound := inverseSquareBlock_index_bounds hKL (hSblock hjS)
    have htail : 4 * K ≤ 2 * j.val := by omega
    rw [thermodynamicPairTailPhaseWeight_matching, if_pos htail,
      abs_of_nonneg (by positivity)]

theorem sum_thermodynamicPairTail_bridge_firstEndpoint_le_Ioc
    {N K : ℕ} (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL) :
    (∑ j : Fin ((N + 2) - 1), if nestedBridgeRight j ∈ S then
        |thermodynamicPairTailPhaseWeight N K (nestedBridgeEdge j)| else 0) ≤
      ∑ n ∈ Finset.Ioc (4 * K) (N + 2), (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [← sum_bridge_tail_indicator_eq_Ioc (N + 2) (4 * K) (by omega)]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hright : nestedBridgeRight j ∈ S
  · have hbound := inverseSquareBlock_index_bounds hKL (hSblock hright)
    have hgt : 4 * K < j.val + 2 := by
      change 4 * K < j.val + 2 ∧ j.val + 2 ≤ 8 * K at hbound
      exact hbound.1
    have htail : 4 * K ≤ 2 * j.val + 1 := by omega
    rw [if_pos hright, thermodynamicPairTailPhaseWeight_bridge, if_pos htail,
      abs_of_nonneg (by positivity), if_pos hgt]
  · rw [if_neg hright]
    positivity

theorem sum_thermodynamicPairTail_bridge_firstEndpoint_le_inv_cube
    {N K : ℕ} (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL) :
    (∑ j : Fin ((N + 2) - 1), if nestedBridgeRight j ∈ S then
        |thermodynamicPairTailPhaseWeight N K (nestedBridgeEdge j)| else 0) ≤
      1 / ((4 * K : ℕ) : ℝ) ^ 3 := by
  have hbridge := sum_thermodynamicPairTail_bridge_firstEndpoint_le_Ioc
    hK hKL S hSblock
  have htail := sum_inv_fourth_Ioc_le (4 * K) (by omega) (N + 2) (by omega)
  have hnonneg : 0 ≤ 1 / ((N + 2 : ℕ) : ℝ) ^ 3 := by positivity
  linarith

theorem thermodynamicPairTailCrossingWeight_firstEndpoint_lower
    {N K : ℕ} (hKL : 8 * K ≤ N + 2)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL) :
    (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) ≤
      thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) := by
  rw [thermodynamicPairTailCrossingWeight_firstEndpoint_expand,
    sum_thermodynamicPairTail_matching_firstEndpoint hKL S hSblock]
  have hbridge : 0 ≤ ∑ j : Fin ((N + 2) - 1),
      if nestedBridgeRight j ∈ S then
        |thermodynamicPairTailPhaseWeight N K (nestedBridgeEdge j)| else 0 := by
    positivity
  linarith

theorem thermodynamicPairTailCrossingWeight_firstEndpoint_upper
    {N K : ℕ} (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL) :
    thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) ≤
      (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
        1 / ((4 * K : ℕ) : ℝ) ^ 3 := by
  rw [thermodynamicPairTailCrossingWeight_firstEndpoint_expand,
    sum_thermodynamicPairTail_matching_firstEndpoint hKL S hSblock]
  simpa [add_comm] using add_le_add_left
    (sum_thermodynamicPairTail_bridge_firstEndpoint_le_inv_cube hK hKL S hSblock)
    (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2))

/-- Tree orientation chooses four configurations whose tail-center mixed energy is the full
positive crossing weight. -/
theorem exists_thermodynamicPairTailCenterEnergy_cut_mixed
    (N K : ℕ) (A : Finset (PairQubit (N + 2))) :
    ∃ sigma : PairQubit (N + 2) → Bool,
      thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false false) +
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true true) -
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma false true) -
          thermodynamicPairTailCenterEnergy N K (cutFourConfig A sigma true false) =
        thermodynamicPairTailCrossingWeight N K A := by
  obtain ⟨sigma, hsigma⟩ := treePhaseEnergy_cut_mixed
    (thermodynamicPairTailGraph N) (thermodynamicPairTailGraph_isTree N)
    (thermodynamicPairTailPhaseWeight N K) A
  refine ⟨sigma, ?_⟩
  rw [thermodynamicPairTailCenterEnergy_cut_mixed_eq_treePhaseEnergy]
  exact hsigma

theorem time_mul_thermodynamicPairTailCrossingWeight_lower
    {N K : ℕ} {t ε : ℝ} (hKL : 8 * K ≤ N + 2) (ht0 : 0 ≤ t)
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL)
    (hphaseLo : 3 * Real.pi * ε ≤ ∑ j ∈ S, inverseSquarePhaseWeight t j) :
    3 * Real.pi * ε ≤
      t * thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) := by
  have hmass := thermodynamicPairTailCrossingWeight_firstEndpoint_lower hKL S hSblock
  have hmul := mul_le_mul_of_nonneg_left hmass ht0
  have hmatch :
      t * (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) =
        ∑ j ∈ S, inverseSquarePhaseWeight t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold inverseSquarePhaseWeight
    ring
  rw [hmatch] at hmul
  exact hphaseLo.trans hmul

theorem time_mul_thermodynamicPairTailCrossingWeight_upper
    {N K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ N + 2) (hε : 0 < ε) (ht0 : 0 ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (S : Finset (Fin (N + 2))) (hSblock : S ⊆ inverseSquareBlock hKL)
    (hphaseHi : ∑ j ∈ S, inverseSquarePhaseWeight t j ≤ 5 * Real.pi * ε) :
    t * thermodynamicPairTailCrossingWeight N K (firstEndpointSites S) <
      5 * Real.pi * ε + ε / 4 := by
  have hmass := thermodynamicPairTailCrossingWeight_firstEndpoint_upper
    hK hKL S hSblock
  have hmul := mul_le_mul_of_nonneg_left hmass ht0
  have hmatch :
      t * (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) =
        ∑ j ∈ S, inverseSquarePhaseWeight t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold inverseSquarePhaseWeight
    ring
  have hbridge := mobilePhaseBridgeTail_lt_quarter hK hε hthi
  rw [mul_add, hmatch] at hmul
  linarith

end

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
