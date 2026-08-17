import GaloisForLFunctions.HTGeometry.CenteredControlledPhaseGate

/-!
# Late-time free-centering upper bound for the monotonicity counterexample
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def counterKeptMatchingList : List (Fin 16384) :=
  List.ofFn counterKeptMatchingIndexEmbedding

def counterKeptBridgeList : List (Fin (16384 - 1)) :=
  List.ofFn counterKeptBridgeIndexEmbedding

@[simp] theorem counterKeptMatchingList_length : counterKeptMatchingList.length = 1476 := by
  rw [counterKeptMatchingList, List.length_ofFn]

@[simp] theorem counterKeptBridgeList_length : counterKeptBridgeList.length = 37 := by
  rw [counterKeptBridgeList, List.length_ofFn]

noncomputable def counterFirstCenteredSpec : CenteredPairSpec (PairQubit 16384) where
  left := ((0 : Fin 16384), false)
  right := ((0 : Fin 16384), true)
  theta := 0

noncomputable def counterTailMatchingSpecs : List (CenteredPairSpec (PairQubit 16384)) :=
  List.ofFn fun j : Fin (16384 - 1477) =>
    let k := counterTailMatchingIndexEmbedding j
    { left := (k, false)
      right := (k, true)
      theta := monotonicityCounterLateTime / (((k.val + 1 : ℕ) : ℝ) ^ 2) }

noncomputable def counterTailBridgeSpecs : List (CenteredPairSpec (PairQubit 16384)) :=
  List.ofFn fun j : Fin (16384 - 38) =>
    let k := counterTailBridgeIndexEmbedding j
    { left := (nestedBridgeLeft k, true)
      right := (nestedBridgeRight k, false)
      theta := monotonicityCounterLateTime / (((k.val + 2 : ℕ) : ℝ) ^ 4) }

noncomputable def counterCenteredTailSpecs : List (CenteredPairSpec (PairQubit 16384)) :=
  counterFirstCenteredSpec :: (counterTailMatchingSpecs ++ counterTailBridgeSpecs)

noncomputable def counterLateCircuit : List (LocalGate (PairQubit 16384)) :=
  matchingPhaseCircuit counterKeptMatchingList monotonicityCounterLateTime ++
    nestedBridgePhaseCircuit counterKeptBridgeList monotonicityCounterLateTime ++
      centeredPairCircuit counterCenteredTailSpecs

@[simp] theorem counterLateCircuit_twoGateCount :
    twoGateCount counterLateCircuit = 1513 := by
  rw [counterLateCircuit, twoGateCount_append, twoGateCount_append,
    matchingPhaseCircuit_twoGateCount, nestedBridgePhaseCircuit_twoGateCount,
    centeredPairCircuit_twoGateCount]
  rw [counterKeptMatchingList_length, counterKeptBridgeList_length]

noncomputable def counterLateApproxEnergy (x : Config (PairQubit 16384)) : ℝ :=
  monotonicityCounterLateTime * listMatchingEnergy counterKeptMatchingList x +
    monotonicityCounterLateTime * listNestedBridgeEnergy counterKeptBridgeList x +
      listCenteredPairEnergy counterCenteredTailSpecs x

theorem counterLateCircuit_matrix :
    circuitMatrix counterLateCircuit =
      Matrix.diagonal fun x =>
        Complex.exp (-(Complex.I * (counterLateApproxEnergy x : ℂ))) := by
  rw [counterLateCircuit, circuitMatrix_append, circuitMatrix_append,
    matchingPhaseCircuit_matrix, nestedBridgePhaseCircuit_matrix,
    centeredPairCircuit_matrix, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold counterLateApproxEnergy
  push_cast
  ring

theorem counterKeptMatchingEnergy_expand (x : Config (PairQubit 16384)) :
    listMatchingEnergy counterKeptMatchingList x =
      ∑ j : Fin 1476,
        if x (counterKeptMatchingIndexEmbedding j, false) = true ∧
            x (counterKeptMatchingIndexEmbedding j, true) = true then
          1 / ((((counterKeptMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)
        else 0 := by
  unfold listMatchingEnergy counterKeptMatchingList
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

theorem counterKeptBridgeEnergy_expand (x : Config (PairQubit 16384)) :
    listNestedBridgeEnergy counterKeptBridgeList x =
      ∑ j : Fin 37,
        if x (nestedBridgeLeft (counterKeptBridgeIndexEmbedding j), true) = true ∧
            x (nestedBridgeRight (counterKeptBridgeIndexEmbedding j), false) = true then
          1 / ((((counterKeptBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)
        else 0 := by
  unfold listNestedBridgeEnergy counterKeptBridgeList
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

theorem counterCenteredTailEnergy_expand (x : Config (PairQubit 16384)) :
    listCenteredPairEnergy counterCenteredTailSpecs x =
      (∑ j : Fin (16384 - 1477),
        let k := counterTailMatchingIndexEmbedding j
        centeredPairEnergy (k, false) (k, true)
          (monotonicityCounterLateTime / (((k.val + 1 : ℕ) : ℝ) ^ 2)) x) +
      ∑ j : Fin (16384 - 38),
        let k := counterTailBridgeIndexEmbedding j
        centeredPairEnergy (nestedBridgeLeft k, true) (nestedBridgeRight k, false)
          (monotonicityCounterLateTime / (((k.val + 2 : ℕ) : ℝ) ^ 4)) x := by
  unfold listCenteredPairEnergy counterCenteredTailSpecs
  simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
  have hfirst :
      centeredPairEnergy counterFirstCenteredSpec.left counterFirstCenteredSpec.right
          counterFirstCenteredSpec.theta x = 0 := by
    simp [counterFirstCenteredSpec, centeredPairEnergy]
  rw [hfirst, zero_add]
  unfold counterTailMatchingSpecs counterTailBridgeSpecs
  rw [List.map_ofFn, List.sum_ofFn, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

theorem sum_fin_add {m n : ℕ} (f : Fin (m + n) → ℝ) :
    (∑ i : Fin (m + n), f i) =
      (∑ i : Fin m, f (Fin.castAdd n i)) +
        ∑ j : Fin n, f (Fin.natAdd m j) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

theorem counterMatching_sum_decompose (f : Fin 16384 → ℝ) :
    (∑ j : Fin 16384, f j) =
      f 0 +
        (∑ j : Fin 1476, f (counterKeptMatchingIndexEmbedding j)) +
          ∑ j : Fin (16384 - 1477), f (counterTailMatchingIndexEmbedding j) := by
  rw [Fin.sum_univ_succ]
  have hsplit := sum_fin_add (m := 1476) (n := 16384 - 1477)
      (fun i : Fin (1476 + (16384 - 1477)) => f i.succ)
  change (∑ i : Fin 16383, f i.succ) = _ at hsplit
  rw [hsplit, add_assoc]
  congr 1

theorem counterBridge_sum_decompose (f : Fin (16384 - 1) → ℝ) :
    (∑ j : Fin (16384 - 1), f j) =
      (∑ j : Fin 37, f (counterKeptBridgeIndexEmbedding j)) +
        ∑ j : Fin (16384 - 38), f (counterTailBridgeIndexEmbedding j) := by
  have hsplit := sum_fin_add (m := 37) (n := 16384 - 38)
      (fun i : Fin (37 + (16384 - 38)) => f i)
  change (∑ i : Fin 16383, f i) = _ at hsplit
  rw [hsplit]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Fin.ext
    simp [counterTailBridgeIndexEmbedding]
    omega

noncomputable def counterLateResidualEnergy (x : Config (PairQubit 16384)) : ℝ :=
  (∑ j : Fin (16384 - 1477),
      let k := counterTailMatchingIndexEmbedding j
      (monotonicityCounterLateTime / (((k.val + 1 : ℕ) : ℝ) ^ 2)) / 4 *
        booleanZ (x (k, false)) * booleanZ (x (k, true))) +
    ∑ j : Fin (16384 - 38),
      let k := counterTailBridgeIndexEmbedding j
      (monotonicityCounterLateTime / (((k.val + 2 : ℕ) : ℝ) ^ 4)) / 4 *
        booleanZ (x (nestedBridgeLeft k, true)) *
          booleanZ (x (nestedBridgeRight k, false))

theorem counterLateResidualEnergy_abs_le (x : Config (PairQubit 16384)) :
    |counterLateResidualEnergy x| ≤
      monotonicityCounterLateTime * monotonicityCounterTail / 4 := by
  unfold counterLateResidualEnergy
  have htime0 : 0 ≤ monotonicityCounterLateTime := by
    unfold monotonicityCounterLateTime
    positivity
  calc
    |(∑ j : Fin (16384 - 1477),
          let k := counterTailMatchingIndexEmbedding j
          (monotonicityCounterLateTime / (((k.val + 1 : ℕ) : ℝ) ^ 2)) / 4 *
            booleanZ (x (k, false)) * booleanZ (x (k, true))) +
        ∑ j : Fin (16384 - 38),
          let k := counterTailBridgeIndexEmbedding j
          (monotonicityCounterLateTime / (((k.val + 2 : ℕ) : ℝ) ^ 4)) / 4 *
            booleanZ (x (nestedBridgeLeft k, true)) *
              booleanZ (x (nestedBridgeRight k, false))| ≤
        ∑ j : Fin (16384 - 1477),
            |(monotonicityCounterLateTime /
                ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) / 4 *
              booleanZ (x (counterTailMatchingIndexEmbedding j, false)) *
                booleanZ (x (counterTailMatchingIndexEmbedding j, true))| +
          ∑ j : Fin (16384 - 38),
            |(monotonicityCounterLateTime /
                ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) / 4 *
              booleanZ (x (nestedBridgeLeft (counterTailBridgeIndexEmbedding j), true)) *
                booleanZ (x (nestedBridgeRight (counterTailBridgeIndexEmbedding j), false))| := by
      exact le_trans (abs_add_le _ _) (add_le_add (Finset.abs_sum_le_sum_abs _ _)
        (Finset.abs_sum_le_sum_abs _ _))
    _ = monotonicityCounterLateTime / 4 *
          ((∑ j : Fin (16384 - 1477),
              1 / ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) +
            ∑ j : Fin (16384 - 38),
              1 / ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [abs_mul, abs_div, abs_booleanZ, mul_one]
        rw [abs_of_nonneg htime0, abs_of_nonneg (by positivity),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        ring
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [abs_mul, abs_div, abs_booleanZ, mul_one]
        rw [abs_of_nonneg htime0, abs_of_nonneg (by positivity),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        ring
    _ = monotonicityCounterLateTime * monotonicityCounterTail / 4 := by
      have hm :
          (∑ j : Fin (16384 - 1477),
              1 / ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) =
            ∑ n ∈ Finset.Ioc (1477 : ℕ) 16384,
              (1 : ℝ) / (n : ℝ) ^ 2 := by
        refine Finset.sum_bij (fun j _ => (j.val + 1478 : ℕ)) ?_ ?_ ?_ ?_
        · intro j hj; simp; omega
        · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          let j : Fin (16384 - 1477) := ⟨n - 1478, by omega⟩
          exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
        · intro j hj
          simp only [counterTailMatchingIndexEmbedding]
          congr 2
      have hb :
          (∑ j : Fin (16384 - 38),
              1 / ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) =
            ∑ n ∈ Finset.Ioc (38 : ℕ) 16384,
              (1 : ℝ) / (n : ℝ) ^ 4 := by
        refine Finset.sum_bij (fun j _ => (j.val + 39 : ℕ)) ?_ ?_ ?_ ?_
        · intro j hj; simp; omega
        · intro i hi j hj hij; exact Fin.ext (Nat.add_right_cancel hij)
        · intro n hn
          have hn' := Finset.mem_Ioc.mp hn
          let j : Fin (16384 - 38) := ⟨n - 39, by omega⟩
          exact ⟨j, Finset.mem_univ _, by simp [j]; omega⟩
        · intro j hj
          simp only [counterTailBridgeIndexEmbedding]
          congr 2
      rw [hm, hb]
      unfold monotonicityCounterTail monotonicityCounterMatchingCutoff
        monotonicityCounterBridgeCutoff monotonicityCounterLength
      ring

theorem counterLate_energy_identity (x : Config (PairQubit 16384)) :
    treePhaseEnergy (nestedQubitPathGraph 16384)
        (nestedFoldedPhase 16384 monotonicityCounterLateTime 0) x =
      counterLateApproxEnergy x + counterLateResidualEnergy x := by
  rw [treePhaseEnergy_nestedFolded_expand (by omega)]
  rw [counterMatching_sum_decompose, counterBridge_sum_decompose]
  simp only [Fin.val_zero, if_true, neg_zero, zero_mul, zero_add]
  unfold counterLateApproxEnergy counterLateResidualEnergy
  rw [counterKeptMatchingEnergy_expand, counterKeptBridgeEnergy_expand,
    counterCenteredTailEnergy_expand]
  simp only [nestedMatchingEdge, nestedBridgeEdge, edgeP11Value_mk]
  have hkm :
      (∑ j : Fin 1476,
          (if (counterKeptMatchingIndexEmbedding j).val = 0 then 0
            else monotonicityCounterLateTime /
              ((((counterKeptMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) *
            (if x (counterKeptMatchingIndexEmbedding j, false) = true ∧
                x (counterKeptMatchingIndexEmbedding j, true) = true then 1 else 0)) =
        monotonicityCounterLateTime *
          ∑ j : Fin 1476,
            if x (counterKeptMatchingIndexEmbedding j, false) = true ∧
                x (counterKeptMatchingIndexEmbedding j, true) = true then
              1 / ((((counterKeptMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : (counterKeptMatchingIndexEmbedding j).val ≠ 0 := by
      simp [counterKeptMatchingIndexEmbedding]
    rw [if_neg hj0]
    by_cases hactive : x (counterKeptMatchingIndexEmbedding j, false) = true ∧
        x (counterKeptMatchingIndexEmbedding j, true) = true
    · simp only [if_pos hactive]
      ring
    · simp only [if_neg hactive, mul_zero]
  have hkb :
      (∑ j : Fin 37,
          (monotonicityCounterLateTime /
              ((((counterKeptBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) *
            (if x (nestedBridgeLeft (counterKeptBridgeIndexEmbedding j), true) = true ∧
                x (nestedBridgeRight (counterKeptBridgeIndexEmbedding j), false) = true then
              1 else 0)) =
        monotonicityCounterLateTime *
          ∑ j : Fin 37,
            if x (nestedBridgeLeft (counterKeptBridgeIndexEmbedding j), true) = true ∧
                x (nestedBridgeRight (counterKeptBridgeIndexEmbedding j), false) = true then
              1 / ((((counterKeptBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)
            else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hactive :
        x (nestedBridgeLeft (counterKeptBridgeIndexEmbedding j), true) = true ∧
          x (nestedBridgeRight (counterKeptBridgeIndexEmbedding j), false) = true
    · simp only [if_pos hactive]
      ring
    · simp only [if_neg hactive, mul_zero]
  have htm :
      (∑ j : Fin (16384 - 1477),
          (if (counterTailMatchingIndexEmbedding j).val = 0 then 0
            else monotonicityCounterLateTime /
              ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) *
            (if x (counterTailMatchingIndexEmbedding j, false) = true ∧
                x (counterTailMatchingIndexEmbedding j, true) = true then 1 else 0)) =
        (∑ j : Fin (16384 - 1477),
          centeredPairEnergy (counterTailMatchingIndexEmbedding j, false)
            (counterTailMatchingIndexEmbedding j, true)
            (monotonicityCounterLateTime /
              ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) x) +
        ∑ j : Fin (16384 - 1477),
          (monotonicityCounterLateTime /
              ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) / 4 *
            booleanZ (x (counterTailMatchingIndexEmbedding j, false)) *
              booleanZ (x (counterTailMatchingIndexEmbedding j, true)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : (counterTailMatchingIndexEmbedding j).val ≠ 0 := by
      simp [counterTailMatchingIndexEmbedding]
    rw [if_neg hj0]
    have hp := p11_centered_residual
      (counterTailMatchingIndexEmbedding j, false)
      (counterTailMatchingIndexEmbedding j, true)
      (monotonicityCounterLateTime /
        ((((counterTailMatchingIndexEmbedding j).val + 1 : ℕ) : ℝ) ^ 2)) x
    linarith
  have htb :
      (∑ j : Fin (16384 - 38),
          (monotonicityCounterLateTime /
              ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) *
            (if x (nestedBridgeLeft (counterTailBridgeIndexEmbedding j), true) = true ∧
                x (nestedBridgeRight (counterTailBridgeIndexEmbedding j), false) = true then
              1 else 0)) =
        (∑ j : Fin (16384 - 38),
          centeredPairEnergy (nestedBridgeLeft (counterTailBridgeIndexEmbedding j), true)
            (nestedBridgeRight (counterTailBridgeIndexEmbedding j), false)
            (monotonicityCounterLateTime /
              ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) x) +
        ∑ j : Fin (16384 - 38),
          (monotonicityCounterLateTime /
              ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) / 4 *
            booleanZ (x (nestedBridgeLeft (counterTailBridgeIndexEmbedding j), true)) *
              booleanZ (x (nestedBridgeRight (counterTailBridgeIndexEmbedding j), false)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hp := p11_centered_residual
      (nestedBridgeLeft (counterTailBridgeIndexEmbedding j), true)
      (nestedBridgeRight (counterTailBridgeIndexEmbedding j), false)
      (monotonicityCounterLateTime /
        ((((counterTailBridgeIndexEmbedding j).val + 2 : ℕ) : ℝ) ^ 4)) x
    linarith
  rw [hkm, hkb, htm, htb]
  ring

theorem counterLateCircuit_approximates :
    NestedOperatorApproximates monotonicityCounterLateTime
      monotonicityCounterEpsilon counterLateCircuit := by
  unfold NestedOperatorApproximates
  apply le_of_lt
  have hε : 0 < monotonicityCounterEpsilon := by
    norm_num [monotonicityCounterEpsilon]
  have hsδ : monotonicityCounterLateTime + 0 = 2 * Real.pi := by
    unfold monotonicityCounterLateTime
    ring
  rw [← nestedFoldedPhaseEvolution_eq (L := 16384) (by omega) hsδ]
  rw [counterLateCircuit_matrix]
  unfold treePhaseEvolution
  rw [l2_opNorm_diagonal_sub, pi_norm_lt_iff hε]
  intro x
  have hphase := norm_exp_phase_sub_le (counterLateApproxEnergy x)
    (treePhaseEnergy (nestedQubitPathGraph 16384)
      (nestedFoldedPhase 16384 monotonicityCounterLateTime 0) x)
  rw [counterLate_energy_identity] at hphase
  have hdiff :
      |counterLateApproxEnergy x -
        (counterLateApproxEnergy x + counterLateResidualEnergy x)| =
          |counterLateResidualEnergy x| := by
    rw [sub_add_cancel_left, abs_neg]
  rw [hdiff] at hphase
  have hres := counterLateResidualEnergy_abs_le x
  have htail := monotonicityCounterLateTail_lt_fourEpsilon
  have hsmall :
      monotonicityCounterLateTime * monotonicityCounterTail / 4 <
        monotonicityCounterEpsilon := by
    linarith
  rw [counterLate_energy_identity]
  exact lt_of_le_of_lt hphase (lt_of_le_of_lt hres hsmall)

theorem monotonicityCounterLate_complexity_upper :
    nestedOperatorTwoGateComplexity monotonicityCounterLength
      monotonicityCounterEpsilon monotonicityCounterLateTime ≤ (1513 : ℕ∞) := by
  have h := nestedOperatorTwoGateComplexity_le_of_circuit
    counterLateCircuit_approximates
  simpa [monotonicityCounterLength] using h

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
