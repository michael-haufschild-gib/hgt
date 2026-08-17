import GaloisForLFunctions.HTGeometry.NestedPathEdgeDecomposition

/-!
# Principal folded phases for the nested inverse-power path
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Signed phases at a time `s = 2π - δ`: the first matching phase is represented by `-δ`, all
other path phases by their unfurled positive values. -/
noncomputable def nestedFoldedPhase (L : ℕ) (s δ : ℝ)
    (e : Sym2 (PairQubit L)) : ℝ :=
  (∑ j : Fin L, if nestedMatchingEdge j = e then
      if j.val = 0 then -δ else s / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0) +
    ∑ k : Fin (L - 1), if nestedBridgeEdge k = e then
      s / (((k.val + 2 : ℕ) : ℝ) ^ 4) else 0

theorem nestedFoldedPhase_matching {L : ℕ} (s δ : ℝ) (j : Fin L) :
    nestedFoldedPhase L s δ (nestedMatchingEdge j) =
      if j.val = 0 then -δ else s / (((j.val + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  unfold nestedFoldedPhase
  rw [Finset.sum_eq_single j]
  · have hbridge : (∑ k : Fin (L - 1),
        if nestedBridgeEdge k = nestedMatchingEdge j then
          s / (((k.val + 2 : ℕ) : ℝ) ^ 4) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg]
      exact (nestedMatchingEdge_ne_bridgeEdge j k).symm
    rw [hbridge, add_zero]
    simp
  · intro i hi hij
    rw [if_neg]
    exact fun h => hij (nestedMatchingEdge_injective h)
  · simp

theorem nestedFoldedPhase_bridge {L : ℕ} (s δ : ℝ) (k : Fin (L - 1)) :
    nestedFoldedPhase L s δ (nestedBridgeEdge k) =
      s / (((k.val + 2 : ℕ) : ℝ) ^ 4) := by
  classical
  unfold nestedFoldedPhase
  have hmatch : (∑ j : Fin L, if nestedMatchingEdge j = nestedBridgeEdge k then
      (if j.val = 0 then -δ else s / (((j.val + 1 : ℕ) : ℝ) ^ 2)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    exact nestedMatchingEdge_ne_bridgeEdge j k
  rw [hmatch, zero_add, Finset.sum_eq_single k]
  · simp
  · intro i hi hik
    rw [if_neg]
    exact fun h => hik (nestedBridgeEdge_injective h)
  · simp

def firstMatchingOccupation {L : ℕ} (hL : 0 < L) (x : Config (PairQubit L)) : ℝ :=
  if x (⟨0, hL⟩, false) = true ∧ x (⟨0, hL⟩, true) = true then 1 else 0

theorem treePhaseEnergy_nestedFolded_expand {L : ℕ} (hL : 0 < L)
    (s δ : ℝ) (x : Config (PairQubit L)) :
    treePhaseEnergy (nestedQubitPathGraph L) (nestedFoldedPhase L s δ) x =
      (∑ j : Fin L,
        (if j.val = 0 then -δ else s / (((j.val + 1 : ℕ) : ℝ) ^ 2)) *
          edgeP11Value x (nestedMatchingEdge j)) +
      ∑ k : Fin (L - 1),
        (s / (((k.val + 2 : ℕ) : ℝ) ^ 4)) *
          edgeP11Value x (nestedBridgeEdge k) := by
  classical
  rw [treePhaseEnergy, nestedPath_edgeFinset_eq_union hL]
  rw [Finset.sum_union (nestedMatchingEdges_disjoint_bridgeEdges L)]
  congr 1
  · rw [nestedMatchingEdges]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [nestedFoldedPhase_matching]
    · exact fun _ _ _ _ h => nestedMatchingEdge_injective h
  · rw [nestedBridgeEdges]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [nestedFoldedPhase_bridge]
    · exact fun _ _ _ _ h => nestedBridgeEdge_injective h

theorem treePhaseEnergy_nestedFolded_eq {L : ℕ} (hL : 0 < L)
    {s δ : ℝ} (hsδ : s + δ = 2 * Real.pi) (x : Config (PairQubit L)) :
    treePhaseEnergy (nestedQubitPathGraph L) (nestedFoldedPhase L s δ) x =
      s * nestedInversePowerChainEnergy x -
        2 * Real.pi * firstMatchingOccupation hL x := by
  cases L with
  | zero => omega
  | succ n =>
      rw [treePhaseEnergy_nestedFolded_expand hL]
      unfold nestedInversePowerChainEnergy inverseSquareMatchingEnergy
        nestedInverseFourthBridgeEnergy firstMatchingOccupation
      simp_rw [Fin.sum_univ_succ]
      simp only [nestedMatchingEdge, nestedBridgeEdge, edgeP11Value_mk,
        Fin.val_zero,
        Fin.val_succ, nestedBridgeLeft, nestedBridgeRight]
      simp only [if_true, Nat.succ_ne_zero, ↓reduceIte, Nat.cast_one, one_pow, div_one]
      rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
      simp_rw [mul_ite, mul_one, mul_zero]
      simp_rw [div_eq_mul_inv]
      have hfirst : -δ = s - 2 * Real.pi := by linarith
      rw [hfirst]
      by_cases hactive : x (0, false) = true ∧ x (0, true) = true
      · simp [hactive]
        ring
      · simp [hactive]

theorem nestedFoldedPhaseEvolution_eq {L : ℕ} (hL : 0 < L)
    {s δ : ℝ} (hsδ : s + δ = 2 * Real.pi) :
    treePhaseEvolution (nestedQubitPathGraph L) (nestedFoldedPhase L s δ) =
      nestedInversePowerChainEvolution L s := by
  rw [nestedInversePowerChainEvolution_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [treePhaseEvolution, Matrix.diagonal_apply_eq, treePhaseEnergy_nestedFolded_eq hL hsδ]
    unfold firstMatchingOccupation
    by_cases hactive : x (⟨0, hL⟩, false) = true ∧ x (⟨0, hL⟩, true) = true
    · rw [if_pos hactive]
      simp only [mul_one]
      rw [show -(Complex.I * ((s * nestedInversePowerChainEnergy x -
          2 * Real.pi : ℝ) : ℂ)) =
          -(Complex.I * ((s * nestedInversePowerChainEnergy x : ℝ) : ℂ)) +
            Complex.I * ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.exp_add]
      have hperiodPos : Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
        rw [show Complex.I * ((2 * Real.pi : ℝ) : ℂ) =
          ((2 * Real.pi : ℝ) : ℂ) * Complex.I by ring]
        rw [Complex.exp_mul_I]
        simp
      rw [hperiodPos, mul_one]
      congr 2
      push_cast
      ring
    · rw [if_neg hactive]
      congr 1
      push_cast
      ring
  · simp [treePhaseEvolution, Matrix.diagonal_apply_ne _ hxy,
      Matrix.diagonal_apply_ne _ hxy]

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
