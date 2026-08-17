import GaloisForLFunctions.HTGeometry.NestedMonotonicityNumerics

/-!
# Phase-tail certificate for the explicit nested path
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

set_option maxRecDepth 100000

def counterKeptMatchingIndexEmbedding : Fin 1476 ↪ Fin 16384 where
  toFun j := ⟨j.val + 1, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))

def counterKeptBridgeIndexEmbedding : Fin 37 ↪ Fin (16384 - 1) where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin (16384 - 1) => x.val) h

def counterKeptMatchingEdgeEmbedding : Fin 1476 ↪ Sym2 (PairQubit 16384) where
  toFun j := nestedMatchingEdge (counterKeptMatchingIndexEmbedding j)
  inj' := by
    intro i j h
    exact counterKeptMatchingIndexEmbedding.injective (nestedMatchingEdge_injective h)

def counterKeptBridgeEdgeEmbedding : Fin 37 ↪ Sym2 (PairQubit 16384) where
  toFun j := nestedBridgeEdge (counterKeptBridgeIndexEmbedding j)
  inj' := by
    intro i j h
    exact counterKeptBridgeIndexEmbedding.injective (nestedBridgeEdge_injective h)

def counterKeptMatchingEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.map counterKeptMatchingEdgeEmbedding

def counterKeptBridgeEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.map counterKeptBridgeEdgeEmbedding

def counterKeptEdges : Finset (Sym2 (PairQubit 16384)) :=
  counterKeptMatchingEdges ∪ counterKeptBridgeEdges

@[simp] theorem counterKeptMatchingEdges_card : counterKeptMatchingEdges.card = 1476 := by
  simp [counterKeptMatchingEdges]

@[simp] theorem counterKeptBridgeEdges_card : counterKeptBridgeEdges.card = 37 := by
  simp [counterKeptBridgeEdges]

theorem counterKeptMatchingEdges_disjoint_bridgeEdges :
    Disjoint counterKeptMatchingEdges counterKeptBridgeEdges := by
  rw [Finset.disjoint_left]
  intro e heM heB
  rcases Finset.mem_map.mp heM with ⟨i, hi, rfl⟩
  rcases Finset.mem_map.mp heB with ⟨j, hj, hEq⟩
  exact nestedMatchingEdge_ne_bridgeEdge
    (counterKeptMatchingIndexEmbedding i) (counterKeptBridgeIndexEmbedding j) hEq.symm

@[simp] theorem counterKeptEdges_card : counterKeptEdges.card = 1513 := by
  rw [counterKeptEdges, Finset.card_union_of_disjoint counterKeptMatchingEdges_disjoint_bridgeEdges]
  simp

theorem counterKeptEdges_subset_path :
    counterKeptEdges ⊆ (nestedQubitPathGraph 16384).edgeFinset := by
  intro e he
  rw [counterKeptEdges] at he
  rcases Finset.mem_union.mp he with heM | heB
  · rcases Finset.mem_map.mp heM with ⟨i, hi, rfl⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact nestedQubitPathGraph_adj_pair _
  · rcases Finset.mem_map.mp heB with ⟨j, hj, rfl⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact nestedQubitPathGraph_adj_bridge _

theorem counterEarlyTime_pos : 0 < monotonicityCounterEarlyTime := by
  unfold monotonicityCounterEarlyTime monotonicityCounterDelta
  nlinarith [Real.pi_gt_three]

theorem counterDelta_pos : 0 < monotonicityCounterDelta := by
  norm_num [monotonicityCounterDelta]

noncomputable def counterPhaseWeight (e : Sym2 (PairQubit 16384)) : ℝ :=
  |nestedFoldedPhase 16384 monotonicityCounterEarlyTime monotonicityCounterDelta e|

noncomputable def counterPhaseThreshold : ℝ :=
  monotonicityCounterEarlyTime / (1477 : ℝ) ^ 2

theorem counterPhaseWeight_nonneg (e : Sym2 (PairQubit 16384)) :
    0 ≤ counterPhaseWeight e := abs_nonneg _

theorem counterDelta_lt_threshold :
    monotonicityCounterDelta < counterPhaseThreshold := by
  unfold counterPhaseThreshold monotonicityCounterEarlyTime monotonicityCounterDelta
  have hpi := Real.pi_gt_d6
  norm_num at hpi ⊢
  nlinarith

theorem counterKeptPhaseWeight_ge_threshold
    (e : Sym2 (PairQubit 16384)) (he : e ∈ counterKeptEdges) :
    counterPhaseThreshold ≤ counterPhaseWeight e := by
  rw [counterKeptEdges] at he
  rcases Finset.mem_union.mp he with heM | heB
  · rcases Finset.mem_map.mp heM with ⟨j, hj, rfl⟩
    change counterPhaseThreshold ≤ counterPhaseWeight
      (nestedMatchingEdge (counterKeptMatchingIndexEmbedding j))
    rw [counterPhaseWeight, nestedFoldedPhase_matching]
    have hj0 : (counterKeptMatchingIndexEmbedding j).val ≠ 0 := by
      simp [counterKeptMatchingIndexEmbedding]
    rw [if_neg hj0, abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
    unfold counterPhaseThreshold counterKeptMatchingIndexEmbedding
    change monotonicityCounterEarlyTime / (1477 : ℝ) ^ 2 ≤
      monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ 2)
    have hn : ((j.val + 2 : ℕ) : ℝ) ≤ 1477 := by
      exact_mod_cast (by omega : j.val + 2 ≤ 1477)
    have hn0 : (0 : ℝ) < ((j.val + 2 : ℕ) : ℝ) := by positivity
    have hs0 := counterEarlyTime_pos.le
    gcongr
  · rcases Finset.mem_map.mp heB with ⟨j, hj, rfl⟩
    change counterPhaseThreshold ≤ counterPhaseWeight
      (nestedBridgeEdge (counterKeptBridgeIndexEmbedding j))
    rw [counterPhaseWeight, nestedFoldedPhase_bridge,
      abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
    unfold counterPhaseThreshold counterKeptBridgeIndexEmbedding
    change monotonicityCounterEarlyTime / (1477 : ℝ) ^ 2 ≤
      monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ 4)
    have hpow : (((j.val + 2 : ℕ) : ℝ) ^ 4) ≤ (1477 : ℝ) ^ 2 := by
      have hj38 : j.val + 2 ≤ 38 := by omega
      have hbase : (((j.val + 2 : ℕ) : ℝ) ^ 4) ≤ (38 : ℝ) ^ 4 := by
        gcongr
        exact_mod_cast hj38
      norm_num at hbase ⊢
      linarith
    exact div_le_div_of_nonneg_left counterEarlyTime_pos.le (by positivity) hpow

theorem counterOutsidePhaseWeight_le_threshold
    (e : Sym2 (PairQubit 16384))
    (he : e ∈ (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges) :
    counterPhaseWeight e ≤ counterPhaseThreshold := by
  rw [Finset.mem_sdiff] at he
  rcases he with ⟨hePath, heNot⟩
  rw [nestedPath_edgeFinset_eq_union (by omega)] at hePath
  rcases Finset.mem_union.mp hePath with heM | heB
  · rcases (mem_nestedMatchingEdges e).mp heM with ⟨j, rfl⟩
    rw [counterPhaseWeight, nestedFoldedPhase_matching]
    by_cases hj0 : j.val = 0
    · rw [if_pos hj0, abs_neg, abs_of_pos counterDelta_pos]
      exact counterDelta_lt_threshold.le
    · rw [if_neg hj0, abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
      have hjlarge : 1477 ≤ j.val := by
        by_contra hsmall
        have hjlt : j.val < 1477 := by omega
        let i : Fin 1476 := ⟨j.val - 1, by omega⟩
        have hindex : counterKeptMatchingIndexEmbedding i = j := by
          apply Fin.ext
          simp [counterKeptMatchingIndexEmbedding, i]
          omega
        apply heNot
        rw [counterKeptEdges, Finset.mem_union]
        left
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, by rw [counterKeptMatchingEdgeEmbedding, hindex]⟩
      unfold counterPhaseThreshold
      have hden : (1477 : ℝ) ^ 2 ≤ (((j.val + 1 : ℕ) : ℝ) ^ 2) := by
        gcongr
        exact_mod_cast (by omega : 1477 ≤ j.val + 1)
      gcongr
  · rcases (mem_nestedBridgeEdges e).mp heB with ⟨j, rfl⟩
    rw [counterPhaseWeight, nestedFoldedPhase_bridge,
      abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
    have hjlarge : 37 ≤ j.val := by
      by_contra hsmall
      have hjlt : j.val < 37 := by omega
      let i : Fin 37 := ⟨j.val, hjlt⟩
      have hindex : counterKeptBridgeIndexEmbedding i = j := by
        apply Fin.ext
        simp [counterKeptBridgeIndexEmbedding, i]
      apply heNot
      rw [counterKeptEdges, Finset.mem_union]
      right
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, by rw [counterKeptBridgeEdgeEmbedding, hindex]⟩
    unfold counterPhaseThreshold
    have hden : (1477 : ℝ) ^ 2 ≤ (((j.val + 2 : ℕ) : ℝ) ^ 4) := by
      have h39 : 39 ≤ j.val + 2 := by omega
      have hpow : (39 : ℝ) ^ 4 ≤ (((j.val + 2 : ℕ) : ℝ) ^ 4) := by
        gcongr
        exact_mod_cast h39
      norm_num at hpow ⊢
      linarith
    gcongr

def counterFirstMatchingEdge : Sym2 (PairQubit 16384) :=
  nestedMatchingEdge (0 : Fin 16384)

def counterTailMatchingIndexEmbedding : Fin (16384 - 1477) ↪ Fin 16384 where
  toFun j := ⟨j.val + 1477, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))

def counterTailBridgeIndexEmbedding : Fin (16384 - 38) ↪ Fin (16384 - 1) where
  toFun j := ⟨j.val + 37, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val h))

def counterTailMatchingEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.image (fun j => nestedMatchingEdge (counterTailMatchingIndexEmbedding j))

def counterTailBridgeEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.image (fun j => nestedBridgeEdge (counterTailBridgeIndexEmbedding j))

def counterCertifiedTailEdges : Finset (Sym2 (PairQubit 16384)) :=
  {counterFirstMatchingEdge} ∪ counterTailMatchingEdges ∪ counterTailBridgeEdges

theorem counterCertifiedTailEdges_subset_outside :
    counterCertifiedTailEdges ⊆
      (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges := by
  intro e he
  simp only [counterCertifiedTailEdges, Finset.mem_union, Finset.mem_singleton] at he
  rcases he with (heFirst | heM) | heB
  · apply Finset.mem_sdiff.mpr
    constructor
    · rw [heFirst]
      rw [SimpleGraph.mem_edgeFinset]
      exact nestedQubitPathGraph_adj_pair _
    · intro hkeep
      rw [counterKeptEdges] at hkeep
      rcases Finset.mem_union.mp hkeep with hM | hB
      · rcases Finset.mem_map.mp hM with ⟨j, hj, hEq⟩
        have hEq' : counterFirstMatchingEdge =
            nestedMatchingEdge (counterKeptMatchingIndexEmbedding j) := by
          simpa [counterKeptMatchingEdgeEmbedding] using heFirst.symm.trans hEq
        have := nestedMatchingEdge_injective (by
          simpa [counterFirstMatchingEdge] using hEq')
        have hv := congrArg Fin.val this
        simp [counterFirstMatchingEdge, counterKeptMatchingEdgeEmbedding,
          counterKeptMatchingIndexEmbedding] at hv
      · rcases Finset.mem_map.mp hB with ⟨j, hj, hEq⟩
        apply nestedMatchingEdge_ne_bridgeEdge (0 : Fin 16384)
          (counterKeptBridgeIndexEmbedding j)
        simpa [counterFirstMatchingEdge, counterKeptBridgeEdgeEmbedding] using heFirst.symm.trans hEq
  · rcases Finset.mem_image.mp heM with ⟨j, hj, rfl⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [SimpleGraph.mem_edgeFinset]
      exact nestedQubitPathGraph_adj_pair _
    · intro hkeep
      rw [counterKeptEdges] at hkeep
      rcases Finset.mem_union.mp hkeep with hM | hB
      · rcases Finset.mem_map.mp hM with ⟨i, hi, hEq⟩
        have hidx := nestedMatchingEdge_injective hEq
        have hv := congrArg Fin.val hidx
        simp [counterKeptMatchingEdgeEmbedding, counterKeptMatchingIndexEmbedding,
          counterTailMatchingIndexEmbedding] at hv
        omega
      · rcases Finset.mem_map.mp hB with ⟨i, hi, hEq⟩
        exact nestedMatchingEdge_ne_bridgeEdge _ _ hEq
  · rcases Finset.mem_image.mp heB with ⟨j, hj, rfl⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [SimpleGraph.mem_edgeFinset]
      exact nestedQubitPathGraph_adj_bridge _
    · intro hkeep
      rw [counterKeptEdges] at hkeep
      rcases Finset.mem_union.mp hkeep with hM | hB
      · rcases Finset.mem_map.mp hM with ⟨i, hi, hEq⟩
        exact nestedMatchingEdge_ne_bridgeEdge _ _ hEq
      · rcases Finset.mem_map.mp hB with ⟨i, hi, hEq⟩
        have hidx := nestedBridgeEdge_injective hEq
        have hv := congrArg Fin.val hidx
        simp [counterKeptBridgeEdgeEmbedding, counterKeptBridgeIndexEmbedding,
          counterTailBridgeIndexEmbedding] at hv
        omega

theorem counterCertifiedTailEdges_pairwise_disjoint :
    Disjoint ({counterFirstMatchingEdge} : Finset (Sym2 (PairQubit 16384)))
      counterTailMatchingEdges ∧
    Disjoint (({counterFirstMatchingEdge} : Finset (Sym2 (PairQubit 16384))) ∪
      counterTailMatchingEdges) counterTailBridgeEdges := by
  constructor
  · rw [Finset.disjoint_left]
    intro e heFirst heTail
    rw [Finset.mem_singleton] at heFirst
    subst e
    rcases Finset.mem_image.mp heTail with ⟨j, hj, hEq⟩
    have hidx := nestedMatchingEdge_injective hEq.symm
    have hv := congrArg Fin.val hidx
    simp [counterFirstMatchingEdge, counterTailMatchingIndexEmbedding] at hv
  · rw [Finset.disjoint_left]
    intro e heLeft heBridge
    rcases Finset.mem_image.mp heBridge with ⟨j, hj, rfl⟩
    rcases Finset.mem_union.mp heLeft with heFirst | heMatch
    · rw [Finset.mem_singleton] at heFirst
      exact nestedMatchingEdge_ne_bridgeEdge (0 : Fin 16384)
        (counterTailBridgeIndexEmbedding j) (by
          simpa [counterFirstMatchingEdge] using heFirst.symm)
    · rcases Finset.mem_image.mp heMatch with ⟨i, hi, hEq⟩
      exact nestedMatchingEdge_ne_bridgeEdge _ _ hEq

theorem sum_counterTailMatchingEdges :
    ∑ e ∈ counterTailMatchingEdges, counterPhaseWeight e =
      monotonicityCounterEarlyTime *
        ∑ n ∈ Finset.Ioc (1477 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ 2 := by
  rw [counterTailMatchingEdges, Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => (j.val + 1478 : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      simp
      omega
    · intro i hi j hj hij
      exact Fin.ext (Nat.add_right_cancel hij)
    · intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      let j : Fin (16384 - 1477) := ⟨n - 1478, by omega⟩
      exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
    · intro j hj
      rw [counterPhaseWeight, nestedFoldedPhase_matching]
      have hne : (counterTailMatchingIndexEmbedding j).val ≠ 0 := by
        simp [counterTailMatchingIndexEmbedding]
      rw [if_neg hne, abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
      simp [counterTailMatchingIndexEmbedding]
      ring
  · intro i hi j hj hEq
    exact counterTailMatchingIndexEmbedding.injective (nestedMatchingEdge_injective hEq)

theorem sum_counterTailBridgeEdges :
    ∑ e ∈ counterTailBridgeEdges, counterPhaseWeight e =
      monotonicityCounterEarlyTime *
        ∑ n ∈ Finset.Ioc (38 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [counterTailBridgeEdges, Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => (j.val + 39 : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      simp
      omega
    · intro i hi j hj hij
      exact Fin.ext (Nat.add_right_cancel hij)
    · intro n hn
      have hn' := Finset.mem_Ioc.mp hn
      let j : Fin (16384 - 38) := ⟨n - 39, by omega⟩
      exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
    · intro j hj
      rw [counterPhaseWeight, nestedFoldedPhase_bridge,
        abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
      simp [counterTailBridgeIndexEmbedding]
      ring
  · intro i hi j hj hEq
    exact counterTailBridgeIndexEmbedding.injective (nestedBridgeEdge_injective hEq)

theorem counterCertifiedTail_sum :
    ∑ e ∈ counterCertifiedTailEdges, counterPhaseWeight e =
      monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTail := by
  obtain ⟨hfirst, hbridge⟩ := counterCertifiedTailEdges_pairwise_disjoint
  rw [counterCertifiedTailEdges, Finset.sum_union hbridge, Finset.sum_union hfirst,
    Finset.sum_singleton, sum_counterTailMatchingEdges, sum_counterTailBridgeEdges]
  rw [counterPhaseWeight, counterFirstMatchingEdge, nestedFoldedPhase_matching]
  simp only [Fin.val_zero, if_true, abs_neg, abs_of_pos counterDelta_pos]
  unfold monotonicityCounterTail monotonicityCounterMatchingCutoff
    monotonicityCounterBridgeCutoff monotonicityCounterLength
  ring

theorem counterKeptTail_lower :
    monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTail ≤
      ∑ e ∈ (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges,
        counterPhaseWeight e := by
  rw [← counterCertifiedTail_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg counterCertifiedTailEdges_subset_outside
    (fun e he hnot => counterPhaseWeight_nonneg e)

/-- Deleting any `1513` target edges leaves at least the certified early phase tail. -/
theorem counterEveryDeletion_tail_lower
    (N : Finset (Sym2 (PairQubit 16384)))
    (hN : N ⊆ (nestedQubitPathGraph 16384).edgeFinset)
    (hcard : N.card ≤ 1513) :
    monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTail ≤
      ∑ e ∈ (nestedQubitPathGraph 16384).edgeFinset \ N,
        counterPhaseWeight e := by
  have hmajor := tail_sum_le_of_global_threshold
    (nestedQubitPathGraph 16384).edgeFinset counterKeptEdges N
    counterPhaseWeight counterPhaseThreshold counterPhaseWeight_nonneg
    counterKeptEdges_subset_path hN (by simpa using hcard)
    counterOutsidePhaseWeight_le_threshold counterKeptPhaseWeight_ge_threshold
  exact counterKeptTail_lower.trans hmajor

/-- Every allowed deletion leaves a unit-circle chord strictly above `4ε`. -/
theorem counterEveryDeletion_chord
    (N : Finset (Sym2 (PairQubit 16384)))
    (hN : N ⊆ (nestedQubitPathGraph 16384).edgeFinset)
    (hcard : N.card ≤ 1513) :
    4 * monotonicityCounterEpsilon <
      ‖Complex.exp (-(Complex.I *
        ((∑ e ∈ (nestedQubitPathGraph 16384).edgeFinset \ N,
          |nestedFoldedPhase 16384 monotonicityCounterEarlyTime
            monotonicityCounterDelta e| : ℝ) : ℂ))) - 1‖ := by
  let phi : ℝ := ∑ e ∈ (nestedQubitPathGraph 16384).edgeFinset \ N,
    counterPhaseWeight e
  let tau : ℝ := monotonicityCounterDelta +
    monotonicityCounterEarlyTime * monotonicityCounterTail
  have htauphi : tau ≤ phi := counterEveryDeletion_tail_lower N hN hcard
  have htau0 : 0 < tau := lt_of_lt_of_le monotonicityCounterTailPhaseFloor_pos
    (monotonicityCounterEarlyTail_ge_floor)
  have hphiTotal : phi ≤ monotonicityCounterDelta +
      monotonicityCounterEarlyTime * monotonicityCounterTotalNonfirstMass := by
    have hsub : (nestedQubitPathGraph 16384).edgeFinset \ N ⊆
        (nestedQubitPathGraph 16384).edgeFinset := Finset.sdiff_subset
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun e he hnot => counterPhaseWeight_nonneg e)
    -- The full edge mass is exactly the first folded phase plus every nonfirst bond.
    rw [nestedPath_edgeFinset_eq_union (by omega),
      Finset.sum_union (nestedMatchingEdges_disjoint_bridgeEdges 16384)] at hsum
    rw [nestedMatchingEdges, nestedBridgeEdges, Finset.sum_image, Finset.sum_image] at hsum
    · simp_rw [counterPhaseWeight, nestedFoldedPhase_matching]
      simp_rw [counterPhaseWeight, nestedFoldedPhase_bridge]
      have hmatch :
          ∑ j : Fin 16384,
              |if j.val = 0 then -monotonicityCounterDelta
                else monotonicityCounterEarlyTime / (((j.val + 1 : ℕ) : ℝ) ^ 2)| =
            monotonicityCounterDelta + monotonicityCounterEarlyTime *
              ∑ n ∈ Finset.Ioc 1 16384, (1 : ℝ) / (n : ℝ) ^ 2 := by
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, if_true, abs_neg, abs_of_pos counterDelta_pos]
        rw [Finset.mul_sum]
        refine congrArg (monotonicityCounterDelta + ·) ?_
        refine Finset.sum_bij (fun j _ => j.val + 2) ?_ ?_ ?_ ?_
        · intro j hj; simp; omega
        · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
        · intro n hn
          let j : Fin 16383 := ⟨n - 2, by have := Finset.mem_Ioc.mp hn; omega⟩
          exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
        · intro j hj
          rw [if_neg (by simp)]
          rw [abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
          simp
          ring
      have hbridge :
          ∑ j : Fin (16384 - 1),
              |monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ 4)| =
            monotonicityCounterEarlyTime *
              ∑ n ∈ Finset.Ioc 1 16384, (1 : ℝ) / (n : ℝ) ^ 4 := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun j _ => j.val + 2) ?_ ?_ ?_ ?_
        · intro j hj; simp; omega
        · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
        · intro n hn
          let j : Fin (16384 - 1) := ⟨n - 2, by have := Finset.mem_Ioc.mp hn; omega⟩
          exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
        · intro j hj
          rw [abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
          ring
      rw [hmatch, hbridge] at hsum
      simpa [phi, monotonicityCounterTotalNonfirstMass,
        monotonicityCounterLength, add_assoc, mul_add] using hsum
    · exact fun _ _ _ _ h => nestedBridgeEdge_injective h
    · exact fun _ _ _ _ h => nestedMatchingEdge_injective h
  apply phase_chord_gt_four_mul_of_tail_interval htau0 htauphi
    (lt_of_le_of_lt hphiTotal monotonicityCounterTotalPhase_lt_threePiOverTwo)
    monotonicityCounterEarlyTail_sub_cube_gt monotonicityCounterSmallError

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
