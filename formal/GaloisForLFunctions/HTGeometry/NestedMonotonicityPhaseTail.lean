import GaloisForLFunctions.HTGeometry.NestedMonotonicityNumerics

/-!
# Phase-tail certificate for the explicit nested path
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

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

def counterAllMatchingEdgeEmbedding : Fin 16384 ↪ Sym2 (PairQubit 16384) where
  toFun := nestedMatchingEdge
  inj' := nestedMatchingEdge_injective

def counterAllBridgeEdgeEmbedding : Fin (16384 - 1) ↪ Sym2 (PairQubit 16384) where
  toFun := nestedBridgeEdge
  inj' := nestedBridgeEdge_injective

def counterKeptMatchingEdgeEmbedding : Fin 1476 ↪ Sym2 (PairQubit 16384) :=
  counterKeptMatchingIndexEmbedding.trans counterAllMatchingEdgeEmbedding

def counterKeptBridgeEdgeEmbedding : Fin 37 ↪ Sym2 (PairQubit 16384) :=
  counterKeptBridgeIndexEmbedding.trans counterAllBridgeEdgeEmbedding

def counterKeptMatchingEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.map counterKeptMatchingEdgeEmbedding

def counterKeptBridgeEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.map counterKeptBridgeEdgeEmbedding

def counterKeptEdgeEmbedding : (Fin 1476 ⊕ Fin 37) ↪ Sym2 (PairQubit 16384) where
  toFun
    | Sum.inl j => nestedMatchingEdge (counterKeptMatchingIndexEmbedding j)
    | Sum.inr j => nestedBridgeEdge (counterKeptBridgeIndexEmbedding j)
  inj' := by
    intro i j h
    cases i with
    | inl i =>
        cases j with
        | inl j =>
            simp only [Sum.inl.injEq]
            exact counterKeptMatchingIndexEmbedding.injective (nestedMatchingEdge_injective h)
        | inr j => exact (nestedMatchingEdge_ne_bridgeEdge _ _ h).elim
    | inr i =>
        cases j with
        | inl j => exact (nestedMatchingEdge_ne_bridgeEdge _ _ h.symm).elim
        | inr j =>
            simp only [Sum.inr.injEq]
            exact counterKeptBridgeIndexEmbedding.injective (nestedBridgeEdge_injective h)

def counterKeptEdges : Finset (Sym2 (PairQubit 16384)) :=
  Finset.univ.map counterKeptEdgeEmbedding

@[simp] theorem counterKeptMatchingEdges_card : counterKeptMatchingEdges.card = 1476 := by
  simp [counterKeptMatchingEdges]

@[simp] theorem counterKeptBridgeEdges_card : counterKeptBridgeEdges.card = 37 := by
  simp [counterKeptBridgeEdges]

theorem counterKeptMatchingEdges_disjoint_bridgeEdges :
    Disjoint counterKeptMatchingEdges counterKeptBridgeEdges := by
  classical
  rw [Finset.disjoint_left]
  intro e heM heB
  rcases Finset.mem_map.mp heM with ⟨i, hi, rfl⟩
  rcases Finset.mem_map.mp heB with ⟨j, hj, hEq⟩
  exact nestedMatchingEdge_ne_bridgeEdge
    (counterKeptMatchingIndexEmbedding i) (counterKeptBridgeIndexEmbedding j) hEq.symm

@[simp] theorem counterKeptEdges_card : counterKeptEdges.card = 1513 := by
  simp [counterKeptEdges]

theorem counterKeptEdges_subset_path :
    counterKeptEdges ⊆ (nestedQubitPathGraph 16384).edgeFinset := by
  classical
  intro e he
  rw [counterKeptEdges] at he
  rcases Finset.mem_map.mp he with ⟨j, hj, hEq⟩
  rw [← hEq]
  cases j with
  | inl j =>
      rw [SimpleGraph.mem_edgeFinset]
      exact nestedQubitPathGraph_adj_pair _
  | inr j =>
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
  monotonicityCounterEarlyTime / (1477 : ℝ) ^ (2 : ℕ)

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
  classical
  rw [counterKeptEdges] at he
  rcases Finset.mem_map.mp he with ⟨j, hj, rfl⟩
  cases j with
  | inl j =>
    change counterPhaseThreshold ≤ counterPhaseWeight
      (nestedMatchingEdge (counterKeptMatchingIndexEmbedding j))
    rw [counterPhaseWeight, nestedFoldedPhase_matching]
    have hj0 : (counterKeptMatchingIndexEmbedding j).val ≠ 0 := by
      simp [counterKeptMatchingIndexEmbedding]
    rw [if_neg hj0, abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
    unfold counterPhaseThreshold counterKeptMatchingIndexEmbedding
    change monotonicityCounterEarlyTime / (1477 : ℝ) ^ (2 : ℕ) ≤
      monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ (2 : ℕ))
    have hn : ((j.val + 2 : ℕ) : ℝ) ≤ 1477 := by
      exact_mod_cast (by omega : j.val + 2 ≤ 1477)
    have hn0 : (0 : ℝ) < ((j.val + 2 : ℕ) : ℝ) := by positivity
    have hs0 := counterEarlyTime_pos.le
    gcongr
  | inr j =>
    change counterPhaseThreshold ≤ counterPhaseWeight
      (nestedBridgeEdge (counterKeptBridgeIndexEmbedding j))
    rw [counterPhaseWeight, nestedFoldedPhase_bridge,
      abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
    unfold counterPhaseThreshold counterKeptBridgeIndexEmbedding
    change monotonicityCounterEarlyTime / (1477 : ℝ) ^ (2 : ℕ) ≤
      monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ))
    have hpow : (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ)) ≤ (1477 : ℝ) ^ (2 : ℕ) := by
      have hj38 : j.val + 2 ≤ 38 := by omega
      have hbase : (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ)) ≤ (38 : ℝ) ^ (4 : ℕ) := by
        gcongr
        exact_mod_cast hj38
      norm_num at hbase ⊢
      linarith
    exact div_le_div_of_nonneg_left counterEarlyTime_pos.le (by positivity) hpow

theorem counterOutsidePhaseWeight_le_threshold
    (e : Sym2 (PairQubit 16384))
    (he : e ∈ (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges) :
    counterPhaseWeight e ≤ counterPhaseThreshold := by
  classical
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
        rw [counterKeptEdges]
        exact Finset.mem_map.mpr ⟨Sum.inl i, Finset.mem_univ _, by
          simpa [counterKeptEdgeEmbedding] using congrArg nestedMatchingEdge hindex⟩
      unfold counterPhaseThreshold
      have hden : (1477 : ℝ) ^ (2 : ℕ) ≤ (((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        gcongr
        exact_mod_cast (by omega : 1477 ≤ j.val + 1)
      exact div_le_div_of_nonneg_left counterEarlyTime_pos.le (by positivity) hden
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
      rw [counterKeptEdges]
      exact Finset.mem_map.mpr ⟨Sum.inr i, Finset.mem_univ _, by
        simpa [counterKeptEdgeEmbedding] using congrArg nestedBridgeEdge hindex⟩
    unfold counterPhaseThreshold
    have hden : (1477 : ℝ) ^ (2 : ℕ) ≤ (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ)) := by
      have h39 : 39 ≤ j.val + 2 := by omega
      have hpow : (39 : ℝ) ^ (4 : ℕ) ≤ (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ)) := by
        gcongr
        exact_mod_cast h39
      norm_num at hpow ⊢
      linarith
    exact div_le_div_of_nonneg_left counterEarlyTime_pos.le (by positivity) hden

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

theorem counterFirstMatchingEdge_mem_outside :
    counterFirstMatchingEdge ∈
      (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges := by
  classical
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [counterFirstMatchingEdge, SimpleGraph.mem_edgeFinset]
    exact nestedQubitPathGraph_adj_pair _
  · rw [counterKeptEdges]
    intro hK
    rcases Finset.mem_map.mp hK with ⟨j, hj, hEq⟩
    cases j with
    | inl j =>
        have hidx := nestedMatchingEdge_injective (by
          simpa [counterFirstMatchingEdge, counterKeptEdgeEmbedding] using hEq.symm)
        have hv := congrArg Fin.val hidx
        simp [counterKeptMatchingIndexEmbedding] at hv
    | inr j =>
        apply nestedMatchingEdge_ne_bridgeEdge (0 : Fin 16384)
          (counterKeptBridgeIndexEmbedding j)
        simpa [counterFirstMatchingEdge, counterKeptEdgeEmbedding] using hEq.symm

theorem counterTailMatchingEdges_subset_outside :
    counterTailMatchingEdges ⊆
      (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges := by
  classical
  intro e he
  rw [counterTailMatchingEdges] at he
  rcases Finset.mem_image.mp he with ⟨j, hj, hEq⟩
  rw [← hEq]
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [SimpleGraph.mem_edgeFinset]
    exact nestedQubitPathGraph_adj_pair _
  · rw [counterKeptEdges]
    intro hK
    rcases Finset.mem_map.mp hK with ⟨i, hi, hEq⟩
    cases i with
    | inl i =>
        have hidx := nestedMatchingEdge_injective (by
          simpa [counterKeptEdgeEmbedding] using hEq)
        have hv := congrArg Fin.val hidx
        simp [counterKeptMatchingIndexEmbedding, counterTailMatchingIndexEmbedding] at hv
        omega
    | inr i =>
        exact nestedMatchingEdge_ne_bridgeEdge _ _ (by
          simpa [counterKeptEdgeEmbedding] using hEq.symm)

theorem counterTailBridgeEdges_subset_outside :
    counterTailBridgeEdges ⊆
      (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges := by
  classical
  intro e he
  rw [counterTailBridgeEdges] at he
  rcases Finset.mem_image.mp he with ⟨j, hj, hEq⟩
  rw [← hEq]
  apply Finset.mem_sdiff.mpr
  constructor
  · rw [SimpleGraph.mem_edgeFinset]
    exact nestedQubitPathGraph_adj_bridge _
  · rw [counterKeptEdges]
    intro hK
    rcases Finset.mem_map.mp hK with ⟨i, hi, hEq⟩
    cases i with
    | inl i =>
        exact nestedMatchingEdge_ne_bridgeEdge _ _ (by
          simpa [counterKeptEdgeEmbedding] using hEq)
    | inr i =>
        have hidx := nestedBridgeEdge_injective (by
          simpa [counterKeptEdgeEmbedding] using hEq)
        have hv := congrArg Fin.val hidx
        simp [counterKeptBridgeIndexEmbedding, counterTailBridgeIndexEmbedding] at hv
        omega

theorem counterCertifiedTailEdges_subset_outside :
    counterCertifiedTailEdges ⊆
      (nestedQubitPathGraph 16384).edgeFinset \ counterKeptEdges := by
  classical
  rw [counterCertifiedTailEdges]
  apply Finset.union_subset
  · apply Finset.union_subset
    · simpa using counterFirstMatchingEdge_mem_outside
    · exact counterTailMatchingEdges_subset_outside
  · exact counterTailBridgeEdges_subset_outside

theorem counterCertifiedTailEdges_pairwise_disjoint :
    Disjoint ({counterFirstMatchingEdge} : Finset (Sym2 (PairQubit 16384)))
      counterTailMatchingEdges ∧
    Disjoint (({counterFirstMatchingEdge} : Finset (Sym2 (PairQubit 16384))) ∪
      counterTailMatchingEdges) counterTailBridgeEdges := by
  classical
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
        ∑ n ∈ Finset.Ioc (1477 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
  classical
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
        ∑ n ∈ Finset.Ioc (38 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ) := by
  classical
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
  classical
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
  classical
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
  classical
  have hmajor := tail_sum_le_of_global_threshold
    (nestedQubitPathGraph 16384).edgeFinset counterKeptEdges N
    counterPhaseWeight counterPhaseThreshold counterPhaseWeight_nonneg
    counterKeptEdges_subset_path hN (by simpa using hcard)
    counterOutsidePhaseWeight_le_threshold counterKeptPhaseWeight_ge_threshold
  exact counterKeptTail_lower.trans hmajor

theorem counterFullPhaseWeight_sum :
    ∑ e ∈ (nestedQubitPathGraph 16384).edgeFinset, counterPhaseWeight e =
      monotonicityCounterDelta +
        monotonicityCounterEarlyTime * monotonicityCounterTotalNonfirstMass := by
  classical
  rw [nestedPath_edgeFinset_eq_union (by omega),
    Finset.sum_union (nestedMatchingEdges_disjoint_bridgeEdges 16384)]
  rw [nestedMatchingEdges, nestedBridgeEdges, Finset.sum_image, Finset.sum_image]
  · simp_rw [counterPhaseWeight, nestedFoldedPhase_matching]
    simp_rw [nestedFoldedPhase_bridge]
    have hmatch :
        ∑ j : Fin 16384,
            |if j.val = 0 then -monotonicityCounterDelta
              else monotonicityCounterEarlyTime / (((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ))| =
          monotonicityCounterDelta + monotonicityCounterEarlyTime *
            ∑ n ∈ Finset.Ioc (1 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, if_true, abs_neg, abs_of_pos counterDelta_pos]
      rw [Finset.mul_sum]
      refine congrArg (monotonicityCounterDelta + ·) ?_
      refine Finset.sum_bij (fun j _ => (j.val + 2 : ℕ)) ?_ ?_ ?_ ?_
      · intro j hj; simp; omega
      · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
      · intro n hn
        have hn' := Finset.mem_Ioc.mp hn
        let j : Fin 16383 := ⟨n - 2, by omega⟩
        exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
      · intro j hj
        rw [if_neg (by simp)]
        rw [abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
        simp
        ring
    have hbridge :
        ∑ j : Fin (16384 - 1),
            |monotonicityCounterEarlyTime / (((j.val + 2 : ℕ) : ℝ) ^ (4 : ℕ))| =
          monotonicityCounterEarlyTime *
            ∑ n ∈ Finset.Ioc (1 : ℕ) 16384, (1 : ℝ) / (n : ℝ) ^ (4 : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => (j.val + 2 : ℕ)) ?_ ?_ ?_ ?_
      · intro j hj; simp; omega
      · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
      · intro n hn
        have hn' := Finset.mem_Ioc.mp hn
        let j : Fin (16384 - 1) := ⟨n - 2, by omega⟩
        exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
      · intro j hj
        rw [abs_of_pos (div_pos counterEarlyTime_pos (by positivity))]
        simp only [Nat.cast_add, Nat.cast_ofNat]
        ring
    rw [hmatch, hbridge]
    unfold monotonicityCounterTotalNonfirstMass monotonicityCounterLength
    ring
  · exact fun _ _ _ _ h => nestedBridgeEdge_injective h
  · exact fun _ _ _ _ h => nestedMatchingEdge_injective h

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
  classical
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
    rw [counterFullPhaseWeight_sum] at hsum
    simpa [phi] using hsum
  apply phase_chord_gt_four_mul_of_tail_interval htau0 htauphi
    (lt_of_le_of_lt hphiTotal monotonicityCounterTotalPhase_lt_threePiOverTwo)
    monotonicityCounterEarlyTail_sub_cube_gt monotonicityCounterSmallError

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
