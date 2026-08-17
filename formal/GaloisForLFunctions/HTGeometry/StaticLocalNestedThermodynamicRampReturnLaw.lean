import GaloisForLFunctions.HTGeometry.StaticLocalExactReturnReflectionLaw
import Mathlib.Analysis.PSeries

/-!
# Nested static-local thermodynamic ramp--return law

This module replaces the volume-dependent bridge coefficient in the laboratory chain by the
fixed bond sequence `(j + 1)⁻⁴`.  The finite chains are exact restrictions of one bounded
infinite-chain diagonal interaction.  The existing phase witness survives, an explicit circuit
gives the matching upper envelope, and factorial-four commensurability gives an exact return and
cost reflection.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ENNReal
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-! ## Inverse-fourth tails -/

/-- The inverse-fourth tail is bounded by its elementary cubic telescoping majorant. -/
theorem sum_inv_fourth_Ioc_le (K : ℕ) (hK : 1 ≤ K) :
    ∀ L : ℕ, K ≤ L →
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4
        ≤ 1 / (K : ℝ) ^ 3 - 1 / (L : ℝ) ^ 3 := by
  intro L
  induction L with
  | zero =>
      intro h
      have : K = 0 := Nat.le_zero.mp h
      omega
  | succ L ih =>
      intro hKL
      rcases Nat.lt_or_ge K (L + 1) with hlt | hge
      · have hKle : K ≤ L := Nat.lt_succ_iff.mp hlt
        rw [Finset.sum_Ioc_succ_top hKle]
        have hprev := ih hKle
        have hLpos : (0 : ℝ) < L := by
          have : 1 ≤ L := le_trans hK hKle
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        have hL1pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
        have hstep : (1 : ℝ) / ((L : ℝ) + 1) ^ 4 ≤
            1 / (L : ℝ) ^ 3 - 1 / ((L : ℝ) + 1) ^ 3 := by
          rw [div_le_iff₀ (pow_pos hL1pos 4)]
          rw [sub_mul]
          field_simp
          nlinarith [sq_nonneg (L : ℝ)]
        have hcast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith [hprev, hstep]
      · have hKeq : K = L + 1 := le_antisymm hKL hge
        subst hKeq
        simp

/-! ## One nested finite family and its infinite completion -/

/-- Fixed inverse-fourth bridge energy.  The bridge ending at one-based pair `n` has weight
`n⁻⁴`, independent of total chain length. -/
noncomputable def nestedInverseFourthBridgeEnergy {L : ℕ}
    (x : Config (PairQubit L)) : ℝ :=
  ∑ j : Fin (L - 1),
    if x (⟨j.val, by omega⟩, true) = true ∧
        x (⟨j.val + 1, by omega⟩, false) = true then
      1 / (((j.val + 2 : ℕ) : ℝ) ^ 4)
    else 0

noncomputable def nestedInversePowerChainEnergy {L : ℕ}
    (x : Config (PairQubit L)) : ℝ :=
  inverseSquareMatchingEnergy x + nestedInverseFourthBridgeEnergy x

noncomputable def nestedInversePowerChainHamiltonian (L : ℕ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal (fun x => (nestedInversePowerChainEnergy x : ℂ))

noncomputable def nestedInversePowerChainEvolution (L : ℕ) (t : ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  unitaryEvolution (nestedInversePowerChainHamiltonian L) t

theorem nestedInversePowerChainEvolution_diagonal (L : ℕ) (t : ℝ) :
    nestedInversePowerChainEvolution L t =
      Matrix.diagonal (fun x =>
        Complex.exp (-(Complex.I * (t * nestedInversePowerChainEnergy x)))) := by
  exact unitaryEvolution_diagonal _ _

theorem nestedInversePowerChainEvolution_unitary (L : ℕ) (t : ℝ) :
    nestedInversePowerChainEvolution L t ∈
      Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
  rw [nestedInversePowerChainEvolution_diagonal]
  apply mem_unitaryGroup_diagonal_general
  intro x
  rw [Complex.norm_exp]
  simp

theorem nestedInverseFourthBridgeEnergy_nonneg {L : ℕ}
    (x : Config (PairQubit L)) : 0 ≤ nestedInverseFourthBridgeEnergy x := by
  unfold nestedInverseFourthBridgeEnergy
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> positivity

theorem nestedInverseFourthBridgeEnergy_pairFourConfig_false_left {L : ℕ}
    (S : Finset (Fin L)) (b : Bool) :
    nestedInverseFourthBridgeEnergy (pairFourConfig S false b) = 0 := by
  simp [nestedInverseFourthBridgeEnergy, pairFourConfig]

theorem nestedInverseFourthBridgeEnergy_pairFourConfig_false_right {L : ℕ}
    (S : Finset (Fin L)) (a : Bool) :
    nestedInverseFourthBridgeEnergy (pairFourConfig S a false) = 0 := by
  simp [nestedInverseFourthBridgeEnergy, pairFourConfig]

theorem nestedInversePowerChainEnergy_pairFourConfig_false_left {L : ℕ}
    (S : Finset (Fin L)) (b : Bool) :
    nestedInversePowerChainEnergy (pairFourConfig S false b) = 0 := by
  simp [nestedInversePowerChainEnergy,
    inverseSquareMatchingEnergy_pairFourConfig_false_left,
    nestedInverseFourthBridgeEnergy_pairFourConfig_false_left]

theorem nestedInversePowerChainEnergy_pairFourConfig_false_right {L : ℕ}
    (S : Finset (Fin L)) (a : Bool) :
    nestedInversePowerChainEnergy (pairFourConfig S a false) = 0 := by
  simp [nestedInversePowerChainEnergy,
    inverseSquareMatchingEnergy_pairFourConfig_false_right,
    nestedInverseFourthBridgeEnergy_pairFourConfig_false_right]

theorem nestedInversePowerChainEnergy_pairFourConfig_true {L : ℕ}
    (S : Finset (Fin L)) :
    nestedInversePowerChainEnergy (pairFourConfig S true true) =
      (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
        nestedInverseFourthBridgeEnergy (pairFourConfig S true true) := by
  rw [nestedInversePowerChainEnergy, inverseSquareMatchingEnergy_pairFourConfig_true]

theorem sum_bridge_tail_indicator_eq_Ioc (L K : ℕ) (hK : 1 ≤ K) :
    (∑ j : Fin (L - 1),
      if K < j.val + 2 then 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) else 0) =
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun j _ => j.val + 2) ?_ ?_ ?_ ?_
  · intro j hj
    have hjlt : j.val < L - 1 := j.isLt
    simp only [Finset.mem_Ioc]
    exact ⟨(Finset.mem_filter.mp hj).2, by omega⟩
  · intro i hi j hj hij
    exact Fin.ext (Nat.add_right_cancel hij)
  · intro n hn
    have hnK : K < n := (Finset.mem_Ioc.mp hn).1
    have hnL : n ≤ L := (Finset.mem_Ioc.mp hn).2
    have hn2 : 2 ≤ n := by omega
    let j : Fin (L - 1) := ⟨n - 2, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · simp [j]
      omega
    · dsimp [j]
      omega
  · intro j hj
    rfl

/-- On the four-corner witness, every active bridge ends in the selected inverse-square block;
therefore all of its weight lies beyond the one-based index `4K`. -/
theorem nestedBridge_pairFour_true_le_block_tail {L K : ℕ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (S : Finset (Fin L))
    (hSblock : S ⊆ inverseSquareBlock hKL) :
    nestedInverseFourthBridgeEnergy (pairFourConfig S true true) ≤
      ∑ n ∈ Finset.Ioc (4 * K) L, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [← sum_bridge_tail_indicator_eq_Ioc L (4 * K) (by omega)]
  unfold nestedInverseFourthBridgeEnergy
  apply Finset.sum_le_sum
  intro j hj
  by_cases hactive :
      pairFourConfig S true true (⟨j.val, by omega⟩, true) = true ∧
        pairFourConfig S true true (⟨j.val + 1, by omega⟩, false) = true
  · have hright : (⟨j.val + 1, by omega⟩ : Fin L) ∈ S := by
      simpa [pairFourConfig] using hactive.2
    have hblock := inverseSquareBlock_index_bounds hKL (hSblock hright)
    have hgt : 4 * K < j.val + 2 := by
      have hgt' := hblock.1
      change 4 * K < (j.val + 1) + 1 at hgt'
      omega
    simp [hactive, hgt]
  · simp [hactive]
    split_ifs <;> positivity

theorem nestedBridge_pairFour_true_le_inv_cube {L K : ℕ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (S : Finset (Fin L))
    (hSblock : S ⊆ inverseSquareBlock hKL) :
    nestedInverseFourthBridgeEnergy (pairFourConfig S true true) ≤
      1 / ((4 * K : ℕ) : ℝ) ^ 3 := by
  have htail := sum_inv_fourth_Ioc_le (4 * K) (by omega) L (by omega)
  have hbridge := nestedBridge_pairFour_true_le_block_tail hK hKL S hSblock
  have hnonneg : 0 ≤ 1 / (L : ℝ) ^ 3 := by positivity
  linarith

theorem time_mul_nestedBridge_pairFour_lt_quarter {L K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε)
    (ht0 : 0 ≤ t) (hthi : t < 128 * Real.pi * ε * (K + 1))
    (S : Finset (Fin L)) (hSblock : S ⊆ inverseSquareBlock hKL) :
    t * nestedInverseFourthBridgeEnergy (pairFourConfig S true true) < ε / 4 := by
  have hb := nestedBridge_pairFour_true_le_inv_cube hK hKL S hSblock
  have hmul : t * nestedInverseFourthBridgeEnergy (pairFourConfig S true true) ≤
      t * (1 / ((4 * K : ℕ) : ℝ) ^ 3) :=
    mul_le_mul_of_nonneg_left hb ht0
  have hKreal : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hscale : 128 * Real.pi * ε * ((K : ℝ) + 1) <
      ε / 4 * (4 * (K : ℝ)) ^ 3 := by
    have hpoly : 32 * ((K : ℝ) + 1) < (K : ℝ) ^ 3 := by
      nlinarith [sq_nonneg ((K : ℝ) - 8)]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hpiScale : 8 * Real.pi * ((K : ℝ) + 1) < (K : ℝ) ^ 3 := by
      nlinarith
    have := mul_lt_mul_of_pos_left hpiScale (mul_pos hε (by norm_num : (0 : ℝ) < 16))
    nlinarith
  have htScale : t < ε / 4 * (4 * (K : ℝ)) ^ 3 := by
    have hthi' : t < 128 * Real.pi * ε * ((K : ℝ) + 1) := by
      exact_mod_cast hthi
    exact lt_trans hthi' hscale
  have htail : t * (1 / ((4 * K : ℕ) : ℝ) ^ 3) < ε / 4 := by
    have hden : (0 : ℝ) < (4 * (K : ℝ)) ^ 3 := by positivity
    rw [mul_one_div]
    norm_num [Nat.cast_mul]
    rw [div_lt_iff₀ hden]
    simpa using htScale
  exact lt_of_le_of_lt hmul htail

/-! ## Support-certified lower envelope -/

set_option maxHeartbeats 800000 in
theorem nestedInversePowerChain_twoGateCount_ge {L K : ℕ}
    (c : List (LocalGate (PairQubit L))) {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (hclose : ‖circuitMatrix c - nestedInversePowerChainEvolution L t‖ ≤ ε) :
    K ≤ twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c < K := Nat.lt_of_not_ge hnot
  rcases circuit_exists_inverseSquare_phase_subset c hK hKL hε htlo hthi hcost with
    ⟨S, hSblock, hSdisj, hphaseLo, hphaseHi⟩
  let x00 := pairFourConfig S false false
  let x01 := pairFourConfig S false true
  let x10 := pairFourConfig S true false
  let x11 := pairFourConfig S true true
  let W := circuitMatrix c
  let U := nestedInversePowerChainEvolution L t
  let φ := t * nestedInversePowerChainEnergy x11
  have htpos : 0 < t := by
    have hKN : 0 < K := by omega
    have hp : 0 < 128 * Real.pi * ε * (K : ℝ) := by positivity
    exact lt_of_lt_of_le hp htlo
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [W, x00, x01, x10, x11]
    exact (circuitMatrix_separates_firstEndpoints c S hSdisj).fourPoint_diagonal
  have hentry (x : Config (PairQubit L)) : ‖U x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - U) x x‖ ≤ ‖W - U‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - U) x x = W x x - U x x := rfl
    rw [hrewrite] at hnorm
    rw [norm_sub_rev] at hnorm
    exact le_trans hnorm hclose
  have hUdiag (x : Config (PairQubit L)) :
      U x x = Complex.exp (-(Complex.I * (t * nestedInversePowerChainEnergy x))) := by
    dsimp only [U]
    rw [nestedInversePowerChainEvolution_diagonal]
    simp
  have hU00 : U x00 x00 = 1 := by
    rw [hUdiag]
    have hz : nestedInversePowerChainEnergy x00 = 0 := by
      exact nestedInversePowerChainEnergy_pairFourConfig_false_left S false
    rw [hz]
    norm_num
  have hU01 : U x01 x01 = 1 := by
    rw [hUdiag]
    have hz : nestedInversePowerChainEnergy x01 = 0 := by
      exact nestedInversePowerChainEnergy_pairFourConfig_false_left S true
    rw [hz]
    norm_num
  have hU10 : U x10 x10 = 1 := by
    rw [hUdiag]
    have hz : nestedInversePowerChainEnergy x10 = 0 := by
      exact nestedInversePowerChainEnergy_pairFourConfig_false_right S true
    rw [hz]
    norm_num
  have hU11 : U x11 x11 = Complex.exp (-(Complex.I * (φ : ℂ))) := by
    rw [hUdiag]
    simp [φ]
  have hmatch :
      t * (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) =
        ∑ j ∈ S, inverseSquarePhaseWeight t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold inverseSquarePhaseWeight
    ring
  have hφsplit : φ = (∑ j ∈ S, inverseSquarePhaseWeight t j) +
      t * nestedInverseFourthBridgeEnergy x11 := by
    dsimp only [φ, x11]
    rw [nestedInversePowerChainEnergy_pairFourConfig_true, mul_add, hmatch]
  have hbridge0 : 0 ≤ t * nestedInverseFourthBridgeEnergy x11 :=
    mul_nonneg (le_of_lt htpos) (nestedInverseFourthBridgeEnergy_nonneg x11)
  have hbridgeHi : t * nestedInverseFourthBridgeEnergy x11 < ε / 4 := by
    dsimp only [x11]
    exact time_mul_nestedBridge_pairFour_lt_quarter hK hKL hε (le_of_lt htpos)
      hthi S hSblock
  have hφ0 : 0 ≤ φ := by
    rw [hφsplit]
    have hp := Real.pi_pos
    linarith
  have hφLo : 3 * Real.pi * ε ≤ φ := by rw [hφsplit]; linarith
  have hφHiRaw : φ < 5 * Real.pi * ε + ε / 4 := by rw [hφsplit]; linarith
  have hφpi : φ ≤ Real.pi := by
    have hp := Real.pi_pos
    have hpieps : Real.pi * ε ≤ Real.pi * (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hεsmall (le_of_lt hp)
    have heps4 : ε / 4 ≤ (1 / 100 : ℝ) / 4 := by linarith
    have hpi3 := Real.pi_gt_three
    have : 5 * Real.pi * ε + ε / 4 < Real.pi := by nlinarith
    exact le_trans (le_of_lt hφHiRaw) (le_of_lt this)
  have h00 : ‖(1 : ℂ) - W x00 x00‖ ≤ ε := by simpa [hU00] using hentry x00
  have h01 : ‖(1 : ℂ) - W x01 x01‖ ≤ ε := by simpa [hU01] using hentry x01
  have h10 : ‖(1 : ℂ) - W x10 x10‖ ≤ ε := by simpa [hU10] using hentry x10
  have h11 : ‖Complex.exp (-(Complex.I * (φ : ℂ))) - W x11 x11‖ ≤ ε := by
    simpa [hU11] using hentry x11
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
    circuitMatrix_unitary c
  have hn01 : ‖W x01 x01‖ ≤ 1 := entry_norm_bound_of_unitary hWunit _ _
  have hn11 : ‖W x11 x11‖ ≤ 1 := entry_norm_bound_of_unitary hWunit _ _
  have hchordHi : ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ ≤ 4 * ε :=
    norm_sub_one_le_four_mul hfactor h00 h01 h10 h11 hn01 hn11
  have hchordLo := phase_chord_lower hφ0 hφpi
  have hsix : 6 * ε ≤ 2 * φ / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    have hp := Real.pi_pos
    nlinarith
  nlinarith

/-! ## Explicit bridge circuit and upper envelope -/

def nestedBridgeLeft {L : ℕ} (j : Fin (L - 1)) : Fin L := ⟨j.val, by omega⟩

def nestedBridgeRight {L : ℕ} (j : Fin (L - 1)) : Fin L := ⟨j.val + 1, by omega⟩

def nestedBridgeSupport {L : ℕ} (j : Fin (L - 1)) : Finset (PairQubit L) :=
  {(nestedBridgeLeft j, true), (nestedBridgeRight j, false)}

@[simp] theorem nestedBridgeSupport_card {L : ℕ} (j : Fin (L - 1)) :
    (nestedBridgeSupport j).card = 2 := by
  rw [nestedBridgeSupport, Finset.card_pair]
  intro h
  have hp := congrArg Prod.fst h
  have hv := congrArg Fin.val hp
  simp [nestedBridgeLeft, nestedBridgeRight] at hv

noncomputable def nestedBridgePhaseValue {L : ℕ} (j : Fin (L - 1)) (θ : ℝ)
    (x : Config (PairQubit L)) : ℂ :=
  if x (nestedBridgeLeft j, true) = true ∧ x (nestedBridgeRight j, false) = true
    then Complex.exp (-(Complex.I * (θ : ℂ))) else 1

noncomputable def nestedBridgePhaseMatrix {L : ℕ} (j : Fin (L - 1)) (θ : ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal (nestedBridgePhaseValue j θ)

theorem nestedBridgePhaseMatrix_unitary {L : ℕ} (j : Fin (L - 1)) (θ : ℝ) :
    nestedBridgePhaseMatrix j θ ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
  apply mem_unitaryGroup_diagonal_general
  intro x
  unfold nestedBridgePhaseValue
  split_ifs
  · rw [Complex.norm_exp]
    simp
  · norm_num

set_option maxHeartbeats 20000 in
theorem nestedBridgePhaseMatrix_separates {L : ℕ} (j : Fin (L - 1)) (θ : ℝ)
    (A : Finset (PairQubit L))
    (hcut : nestedBridgeSupport j ⊆ A ∨ Disjoint (nestedBridgeSupport j) A) :
    SeparatesAcross A (nestedBridgePhaseMatrix j θ) := by
  rcases hcut with hinside | houtside
  · have hj0 : (nestedBridgeLeft j, true) ∈ A :=
      hinside (by simp [nestedBridgeSupport])
    have hj1 : (nestedBridgeRight j, false) ∈ A :=
      hinside (by simp [nestedBridgeSupport])
    let f : On A → ℂ := fun z =>
      if z ⟨(nestedBridgeLeft j, true), hj0⟩ = true ∧
          z ⟨(nestedBridgeRight j, false), hj1⟩ = true
        then Complex.exp (-(Complex.I * (θ : ℂ))) else 1
    rcases separatesAcross_diagonal_fst A f with ⟨MA, MB, hsep⟩
    refine ⟨MA, MB, fun x y => ?_⟩
    rw [← hsep x y]
    by_cases hxy : x = y
    · subst y
      simp [nestedBridgePhaseMatrix, nestedBridgePhaseValue, f]
    · simp [nestedBridgePhaseMatrix, Matrix.diagonal, hxy]
  · have hj0 : (nestedBridgeLeft j, true) ∉ A := by
      intro h
      exact (Finset.disjoint_left.mp houtside) (by simp [nestedBridgeSupport]) h
    have hj1 : (nestedBridgeRight j, false) ∉ A := by
      intro h
      exact (Finset.disjoint_left.mp houtside) (by simp [nestedBridgeSupport]) h
    let f : Off A → ℂ := fun z =>
      if z ⟨(nestedBridgeLeft j, true), hj0⟩ = true ∧
          z ⟨(nestedBridgeRight j, false), hj1⟩ = true
        then Complex.exp (-(Complex.I * (θ : ℂ))) else 1
    rcases separatesAcross_diagonal_snd A f with ⟨MA, MB, hsep⟩
    refine ⟨MA, MB, fun x y => ?_⟩
    rw [← hsep x y]
    by_cases hxy : x = y
    · subst y
      simp [nestedBridgePhaseMatrix, nestedBridgePhaseValue, f]
    · simp [nestedBridgePhaseMatrix, Matrix.diagonal, hxy]

noncomputable def nestedBridgePhaseGate {L : ℕ} (j : Fin (L - 1)) (θ : ℝ) :
    LocalGate (PairQubit L) where
  support := nestedBridgeSupport j
  matrix := nestedBridgePhaseMatrix j θ
  arity_le_two := by simp
  unitary := nestedBridgePhaseMatrix_unitary j θ
  separates := nestedBridgePhaseMatrix_separates j θ

noncomputable def nestedBridgePhaseCircuit {L : ℕ} (js : List (Fin (L - 1))) (t : ℝ) :
    List (LocalGate (PairQubit L)) :=
  js.map (fun j => nestedBridgePhaseGate j (t / (((j.val + 2 : ℕ) : ℝ) ^ 4)))

noncomputable def listNestedBridgeEnergy {L : ℕ} (js : List (Fin (L - 1)))
    (x : Config (PairQubit L)) : ℝ :=
  (js.map fun j =>
    if x (nestedBridgeLeft j, true) = true ∧ x (nestedBridgeRight j, false) = true
      then 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) else 0).sum

set_option maxHeartbeats 20000 in
theorem nestedBridgePhaseCircuit_matrix {L : ℕ} (js : List (Fin (L - 1))) (t : ℝ) :
    circuitMatrix (nestedBridgePhaseCircuit js t) =
      Matrix.diagonal (fun x =>
        Complex.exp (-(Complex.I * (t * listNestedBridgeEnergy js x)))) := by
  induction js with
  | nil =>
      ext x y
      simp [nestedBridgePhaseCircuit, circuitMatrix, listNestedBridgeEnergy]
  | cons j js ih =>
      rw [nestedBridgePhaseCircuit, List.map_cons, circuitMatrix]
      change nestedBridgePhaseMatrix j (t / (((j.val + 2 : ℕ) : ℝ) ^ 4)) *
          circuitMatrix (nestedBridgePhaseCircuit js t) = _
      rw [ih, nestedBridgePhaseMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext x
      unfold nestedBridgePhaseValue listNestedBridgeEnergy
      by_cases hx : x (nestedBridgeLeft j, true) = true ∧
          x (nestedBridgeRight j, false) = true
      · simp only [List.map_cons, List.sum_cons]
        rw [if_pos hx, if_pos hx, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      · simp [hx]

@[simp] theorem nestedBridgePhaseCircuit_twoGateCount {L : ℕ}
    (js : List (Fin (L - 1))) (t : ℝ) :
    twoGateCount (nestedBridgePhaseCircuit js t) = js.length := by
  induction js with
  | nil => simp [nestedBridgePhaseCircuit, twoGateCount]
  | cons j js ih =>
      rw [nestedBridgePhaseCircuit, List.map_cons, twoGateCount]
      have hcard :
          (nestedBridgePhaseGate j (t / (((j.val + 2 : ℕ) : ℝ) ^ 4))).support.card = 2 := by
        simp [nestedBridgePhaseGate]
      rw [if_pos hcard]
      change 1 + twoGateCount (nestedBridgePhaseCircuit js t) = js.length + 1
      rw [ih]
      omega

noncomputable def nestedBridgeWeight {L : ℕ} (x : Config (PairQubit L))
    (j : Fin (L - 1)) : ℝ :=
  if x (nestedBridgeLeft j, true) = true ∧ x (nestedBridgeRight j, false) = true
    then 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) else 0

theorem nestedInverseFourthBridgeEnergy_eq_sum_weight {L : ℕ}
    (x : Config (PairQubit L)) :
    nestedInverseFourthBridgeEnergy x = ∑ j : Fin (L - 1), nestedBridgeWeight x j := by
  rfl

def nestedInitialBridgeEmbedding {L K : ℕ} (hKL : K ≤ L) : Fin (K - 1) → Fin (L - 1) :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le_sub_right hKL 1)⟩

def nestedInitialBridgeList {L K : ℕ} (hKL : K ≤ L) : List (Fin (L - 1)) :=
  List.ofFn (nestedInitialBridgeEmbedding hKL)

@[simp] theorem nestedInitialBridgeList_length {L K : ℕ} (hKL : K ≤ L) :
    (nestedInitialBridgeList hKL).length = K - 1 := by
  simp [nestedInitialBridgeList]

def nestedInitialBridgeIndices (L K : ℕ) : Finset (Fin (L - 1)) :=
  Finset.univ.filter (fun j => j.val < K - 1)

def nestedTailBridgeIndices (L K : ℕ) : Finset (Fin (L - 1)) :=
  Finset.univ.filter (fun j => K - 1 ≤ j.val)

theorem listNestedBridgeEnergy_initial {L K : ℕ} (hKL : K ≤ L)
    (x : Config (PairQubit L)) :
    listNestedBridgeEnergy (nestedInitialBridgeList hKL) x =
      ∑ j ∈ nestedInitialBridgeIndices L K, nestedBridgeWeight x j := by
  unfold listNestedBridgeEnergy nestedInitialBridgeList
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_bij (fun i _ => nestedInitialBridgeEmbedding hKL i) ?_ ?_ ?_ ?_
  · intro i hi
    simp [nestedInitialBridgeIndices, nestedInitialBridgeEmbedding]
  · intro i hi j hj hij
    apply Fin.ext
    simpa [nestedInitialBridgeEmbedding] using congrArg Fin.val hij
  · intro j hj
    have hjK : j.val < K - 1 := (Finset.mem_filter.mp hj).2
    exact ⟨⟨j.val, hjK⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i hi
    rfl

theorem sum_nestedTailBridge_inv_fourth_eq_Ioc (L K : ℕ) (hK : 1 ≤ K) :
    ∑ j ∈ nestedTailBridgeIndices L K,
        1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) =
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4 := by
  refine Finset.sum_bij (fun j _ => j.val + 2) ?_ ?_ ?_ ?_
  · intro j hj
    have hjK : K - 1 ≤ j.val := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_Ioc]
    exact ⟨by omega, by omega⟩
  · intro i hi j hj hij
    exact Fin.ext (Nat.add_right_cancel hij)
  · intro n hn
    have hnK : K < n := (Finset.mem_Ioc.mp hn).1
    have hnL : n ≤ L := (Finset.mem_Ioc.mp hn).2
    have hn2 : 2 ≤ n := by omega
    let j : Fin (L - 1) := ⟨n - 2, by omega⟩
    refine ⟨j, ?_, ?_⟩
    · simp [nestedTailBridgeIndices, j]
      omega
    · dsimp [j]
      omega
  · intro j hj
    rfl

theorem nestedBridgeWeight_nonneg {L : ℕ} (x : Config (PairQubit L))
    (j : Fin (L - 1)) : 0 ≤ nestedBridgeWeight x j := by
  unfold nestedBridgeWeight
  split_ifs <;> positivity

theorem nestedBridgeWeight_le_inv_fourth {L : ℕ} (x : Config (PairQubit L))
    (j : Fin (L - 1)) :
    nestedBridgeWeight x j ≤ 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) := by
  unfold nestedBridgeWeight
  split_ifs
  · exact le_rfl
  · positivity

theorem nestedBridgeEnergy_le_initial_add_tail {L K : ℕ}
    (hK : 1 ≤ K) (hKL : K ≤ L) (x : Config (PairQubit L)) :
    nestedInverseFourthBridgeEnergy x ≤
      listNestedBridgeEnergy (nestedInitialBridgeList hKL) x +
        ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ 4 := by
  rw [nestedInverseFourthBridgeEnergy_eq_sum_weight,
    listNestedBridgeEnergy_initial hKL, ← sum_nestedTailBridge_inv_fourth_eq_Ioc L K hK]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (L - 1) => j.val < K - 1) (nestedBridgeWeight x)
  have hfirst : Finset.univ.filter (fun j : Fin (L - 1) => j.val < K - 1) =
      nestedInitialBridgeIndices L K := rfl
  have htail : Finset.univ.filter (fun j : Fin (L - 1) => ¬j.val < K - 1) =
      nestedTailBridgeIndices L K := by
    ext j
    simp [nestedTailBridgeIndices]
  rw [hfirst, htail] at hsplit
  rw [← hsplit]
  gcongr
  exact nestedBridgeWeight_le_inv_fourth _ _

theorem listNestedBridgeEnergy_initial_le {L K : ℕ}
    (hKL : K ≤ L) (x : Config (PairQubit L)) :
    listNestedBridgeEnergy (nestedInitialBridgeList hKL) x ≤
      nestedInverseFourthBridgeEnergy x := by
  rw [nestedInverseFourthBridgeEnergy_eq_sum_weight,
    listNestedBridgeEnergy_initial hKL]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (L - 1) => j.val < K - 1) (nestedBridgeWeight x)
  have hfirst : Finset.univ.filter (fun j : Fin (L - 1) => j.val < K - 1) =
      nestedInitialBridgeIndices L K := rfl
  have htail : Finset.univ.filter (fun j : Fin (L - 1) => ¬j.val < K - 1) =
      nestedTailBridgeIndices L K := by
    ext j
    simp [nestedTailBridgeIndices]
  rw [hfirst, htail] at hsplit
  rw [← hsplit]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun j _ => nestedBridgeWeight_nonneg x j)

noncomputable def nestedInitialCircuit {L K : ℕ} (hKL : K ≤ L) (t : ℝ) :
    List (LocalGate (PairQubit L)) :=
  matchingPhaseCircuit (initialPairList hKL) t ++
    nestedBridgePhaseCircuit (nestedInitialBridgeList hKL) t

noncomputable def nestedInitialEnergy {L K : ℕ} (hKL : K ≤ L)
    (x : Config (PairQubit L)) : ℝ :=
  listMatchingEnergy (initialPairList hKL) x +
    listNestedBridgeEnergy (nestedInitialBridgeList hKL) x

theorem nestedInitialCircuit_matrix {L K : ℕ} (hKL : K ≤ L) (t : ℝ) :
    circuitMatrix (nestedInitialCircuit hKL t) =
      Matrix.diagonal (fun x =>
        Complex.exp (-(Complex.I * (t * nestedInitialEnergy hKL x)))) := by
  rw [nestedInitialCircuit, circuitMatrix_append, matchingPhaseCircuit_matrix,
    nestedBridgePhaseCircuit_matrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  simp only [nestedInitialEnergy]
  push_cast
  ring

theorem nestedInitialCircuit_twoGateCount {L K : ℕ} (hKL : K ≤ L) (t : ℝ) :
    twoGateCount (nestedInitialCircuit hKL t) = 2 * K - 1 := by
  rw [nestedInitialCircuit, twoGateCount_append,
    initialPairList_twoGateCount, nestedBridgePhaseCircuit_twoGateCount,
    nestedInitialBridgeList_length]
  omega

theorem nestedInitialEnergy_le {L K : ℕ} (hKL : K ≤ L)
    (x : Config (PairQubit L)) :
    nestedInitialEnergy hKL x ≤ nestedInversePowerChainEnergy x := by
  have hm := listMatchingEnergy_initial_le_inverseSquareMatchingEnergy hKL x
  have hb := listNestedBridgeEnergy_initial_le hKL x
  unfold nestedInitialEnergy nestedInversePowerChainEnergy
  linarith

theorem nestedEnergy_sub_initial_le {L K : ℕ}
    (hK : 1 ≤ K) (hKL : K ≤ L) (x : Config (PairQubit L)) :
    nestedInversePowerChainEnergy x - nestedInitialEnergy hKL x ≤
      1 / (K : ℝ) + 1 / (K : ℝ) ^ 3 := by
  have hsq := sum_inv_sq_Ioc_le K hK L hKL
  have hm := inverseSquareMatchingEnergy_le_initial_add_tail hKL x
  have hfourth := sum_inv_fourth_Ioc_le K hK L hKL
  have hb := nestedBridgeEnergy_le_initial_add_tail hK hKL x
  have hL1 : 0 ≤ 1 / (L : ℝ) := by positivity
  have hL3 : 0 ≤ 1 / (L : ℝ) ^ 3 := by positivity
  unfold nestedInversePowerChainEnergy nestedInitialEnergy
  linarith

theorem nested_tail_phase_lt {t ε K R : ℝ}
    (hε : 0 < ε) (ht : 0 ≤ t) (hK : 1 < K)
    (hKlb : 2 * t / ε ≤ K) (hR : R ≤ 1 / K + 1 / K ^ 3) :
    t * R < ε := by
  have hKpos : 0 < K := lt_trans one_pos hK
  have hfirst : t * (1 / K) ≤ ε / 2 := by
    rcases eq_or_lt_of_le ht with hzero | hpos
    · rw [← hzero]
      simp
      linarith
    · rw [mul_one_div, div_le_iff₀ hKpos]
      have hKlb' := hKlb
      rw [div_le_iff₀ hε] at hKlb'
      nlinarith
  have hinv : 1 / K ^ 3 < 1 / K := by
    rw [div_lt_div_iff₀ (pow_pos hKpos 3) hKpos]
    nlinarith [mul_pos hKpos hKpos]
  have hsecond : t * (1 / K ^ 3) ≤ t * (1 / K) :=
    mul_le_mul_of_nonneg_left (le_of_lt hinv) ht
  have hmul := mul_le_mul_of_nonneg_left hR ht
  rw [mul_add] at hmul
  rcases eq_or_lt_of_le ht with hzero | hpos
  · rw [← hzero]
    simpa using hε
  · have hsecondStrict : t * (1 / K ^ 3) < t * (1 / K) :=
      mul_lt_mul_of_pos_left hinv hpos
    linarith

set_option maxHeartbeats 500000 in
theorem nestedInversePowerChain_upper_approximation {L K : ℕ} {t ε : ℝ}
    (hK : 2 ≤ K) (hKL : K ≤ L) (hε : 0 < ε) (ht0 : 0 ≤ t)
    (hKlb : 2 * t / ε ≤ K) :
    ∃ c : List (LocalGate (PairQubit L)),
      twoGateCount c = 2 * K - 1 ∧
      ‖circuitMatrix c - nestedInversePowerChainEvolution L t‖ < ε := by
  let c := nestedInitialCircuit hKL t
  refine ⟨c, nestedInitialCircuit_twoGateCount hKL t, ?_⟩
  rw [nestedInitialCircuit_matrix, nestedInversePowerChainEvolution_diagonal,
    l2_opNorm_diagonal_sub]
  rw [pi_norm_lt_iff hε]
  intro x
  let E₀ := nestedInitialEnergy hKL x
  let E := nestedInversePowerChainEnergy x
  have hE : E₀ ≤ E := nestedInitialEnergy_le hKL x
  have hR : E - E₀ ≤ 1 / (K : ℝ) + 1 / (K : ℝ) ^ 3 :=
    nestedEnergy_sub_initial_le (by omega) hKL x
  have htime : t * (E - E₀) < ε := by
    apply nested_tail_phase_lt hε ht0 (by exact_mod_cast hK)
      (by exact_mod_cast hKlb) hR
  have hphase := norm_exp_phase_sub_le (t * E₀) (t * E)
  have habs : |t * E₀ - t * E| = t * (E - E₀) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ht0, abs_of_nonpos (sub_nonpos.mpr hE)]
    ring
  rw [habs] at hphase
  simpa [Pi.sub_apply, E₀, E] using lt_of_le_of_lt hphase htime

def NestedOperatorApproximates {L : ℕ} (t ε : ℝ)
    (c : List (LocalGate (PairQubit L))) : Prop :=
  ‖circuitMatrix c - nestedInversePowerChainEvolution L t‖ ≤ ε

set_option maxHeartbeats 1000000 in
theorem nestedInversePowerChain_floor_linear_growth {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    (∀ c : List (LocalGate (PairQubit L)),
        NestedOperatorApproximates t ε c →
          ⌊t / (128 * Real.pi * ε)⌋₊ ≤ twoGateCount c) ∧
      ∃ c : List (LocalGate (PairQubit L)),
        twoGateCount c = 2 * ⌈2 * t / ε⌉₊ - 1 ∧
          ‖circuitMatrix c - nestedInversePowerChainEvolution L t‖ < ε := by
  let d : ℝ := 128 * Real.pi * ε
  let Klo : ℕ := ⌊t / d⌋₊
  let Khi : ℕ := ⌈2 * t / ε⌉₊
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) htMin
  have hrho0 : 0 ≤ t / d := le_of_lt (div_pos htpos hd)
  have hKloFloor : (Klo : ℝ) ≤ t / d := Nat.floor_le hrho0
  have hKloRaw : (Klo : ℝ) * d ≤ t := (le_div_iff₀ hd).mp hKloFloor
  have hKloTime : 128 * Real.pi * ε * Klo ≤ t := by
    dsimp [d] at hKloRaw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hKloRaw
  have hKloNext : t < 128 * Real.pi * ε * (Klo + 1) := by
    have hnext : t / d < (Klo : ℝ) + 1 := Nat.lt_floor_add_one (t / d)
    have hnext' : t < ((Klo : ℝ) + 1) * d := (div_lt_iff₀ hd).mp hnext
    dsimp [d] at hnext'
    nlinarith
  have hKloEight : 8 ≤ Klo := by
    rw [Nat.le_floor_iff' (by norm_num)]
    change (8 : ℝ) ≤ t / d
    rw [le_div_iff₀ hd]
    dsimp [d]
    nlinarith
  have hKloL : 8 * Klo ≤ L := by
    have hraw : ε * (128 * Real.pi * (Klo : ℝ)) ≤ ε * ((L : ℝ) / 2) := by
      calc
        ε * (128 * Real.pi * (Klo : ℝ)) = 128 * Real.pi * ε * Klo := by ring
        _ ≤ t := hKloTime
        _ ≤ ε * L / 2 := htLab
        _ = ε * ((L : ℝ) / 2) := by ring
    have hcancel : 128 * Real.pi * (Klo : ℝ) ≤ (L : ℝ) / 2 :=
      le_of_mul_le_mul_left hraw hε
    have hpi := Real.pi_gt_three
    exact_mod_cast (show (8 : ℝ) * Klo ≤ L by
      calc
        (8 : ℝ) * Klo ≤ 128 * Real.pi * Klo := by
          have hKlo0 : (0 : ℝ) ≤ Klo := by positivity
          nlinarith
        _ ≤ (L : ℝ) / 2 := hcancel
        _ ≤ L := by
          have hL0 : (0 : ℝ) ≤ L := by positivity
          linarith)
  have hKhiTwo : 2 ≤ Khi := by
    have hratio : (2 : ℝ) ≤ 2 * t / ε := by
      rw [le_div_iff₀ hε]
      have hpi := Real.pi_gt_three
      nlinarith
    have hceil : 2 * t / ε ≤ (Khi : ℝ) := by
      exact Nat.le_ceil (2 * t / ε)
    exact_mod_cast le_trans hratio hceil
  have hKhiScale : 2 * t / ε ≤ (Khi : ℝ) := Nat.le_ceil (2 * t / ε)
  have hKhiL : Khi ≤ L := by
    rw [Nat.ceil_le]
    rw [div_le_iff₀ hε]
    nlinarith
  constructor
  · intro c hc
    exact nestedInversePowerChain_twoGateCount_ge c hKloEight hKloL hε hεmax
      hKloTime hKloNext hc
  · simpa [Khi] using nestedInversePowerChain_upper_approximation
      hKhiTwo hKhiL hε (le_of_lt htpos) hKhiScale

/-! ## Exact factorial-four return and complexity reflection -/

theorem factorialFourth_mul_invSq_exists {L k : ℕ} (hk0 : 0 < k) (hkL : k ≤ L) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 4) * (1 / (k : ℝ) ^ 2) = N := by
  rcases Nat.dvd_factorial hk0 hkL with ⟨a, ha⟩
  refine ⟨k ^ 2 * a ^ 4, ?_⟩
  rw [ha]
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp

theorem factorialFourth_mul_invFourth_exists {L k : ℕ}
    (hk0 : 0 < k) (hkL : k ≤ L) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 4) * (1 / (k : ℝ) ^ 4) = N := by
  rcases Nat.dvd_factorial hk0 hkL with ⟨a, ha⟩
  refine ⟨a ^ 4, ?_⟩
  rw [ha]
  push_cast
  have hkR : (k : ℝ) ≠ 0 := by positivity
  field_simp

theorem exists_factorialFourth_mul_matchingEnergy {L : ℕ}
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 4) * inverseSquareMatchingEnergy x = N := by
  classical
  have hterm : ∀ j : Fin L, ∃ N : ℕ,
      ((L.factorial : ℝ) ^ 4) *
        (if x (j, false) = true ∧ x (j, true) = true
          then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0) = N := by
    intro j
    by_cases hx : x (j, false) = true ∧ x (j, true) = true
    · rcases factorialFourth_mul_invSq_exists (L := L) (k := j.val + 1)
          (by omega) (by omega) with ⟨N, hN⟩
      exact ⟨N, by simpa [hx] using hN⟩
    · exact ⟨0, by simp [hx]⟩
  choose N hN using hterm
  refine ⟨∑ j : Fin L, N j, ?_⟩
  unfold inverseSquareMatchingEnergy
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  convert hN j using 1
  norm_num

theorem exists_factorialFourth_mul_nestedBridgeEnergy {L : ℕ}
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 4) * nestedInverseFourthBridgeEnergy x = N := by
  classical
  have hterm : ∀ j : Fin (L - 1), ∃ N : ℕ,
      ((L.factorial : ℝ) ^ 4) *
        (if x (nestedBridgeLeft j, true) = true ∧
            x (nestedBridgeRight j, false) = true
          then 1 / (((j.val + 2 : ℕ) : ℝ) ^ 4) else 0) = N := by
    intro j
    by_cases hx : x (nestedBridgeLeft j, true) = true ∧
        x (nestedBridgeRight j, false) = true
    · rcases factorialFourth_mul_invFourth_exists (L := L) (k := j.val + 2)
          (by omega) (by omega) with ⟨N, hN⟩
      exact ⟨N, by simpa [hx] using hN⟩
    · exact ⟨0, by simp [hx]⟩
  choose N hN using hterm
  refine ⟨∑ j : Fin (L - 1), N j, ?_⟩
  unfold nestedInverseFourthBridgeEnergy
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simpa [nestedBridgeLeft, nestedBridgeRight, Nat.cast_add, Nat.cast_ofNat] using hN j

theorem exists_factorialFourth_mul_nestedChainEnergy {L : ℕ}
    (x : Config (PairQubit L)) :
    ∃ N : ℕ, ((L.factorial : ℝ) ^ 4) * nestedInversePowerChainEnergy x = N := by
  rcases exists_factorialFourth_mul_matchingEnergy x with ⟨a, ha⟩
  rcases exists_factorialFourth_mul_nestedBridgeEnergy x with ⟨b, hb⟩
  refine ⟨a + b, ?_⟩
  rw [nestedInversePowerChainEnergy, mul_add, ha, hb]
  push_cast
  rfl

noncomputable def nestedInversePowerReturnPeriod (L : ℕ) : ℝ :=
  2 * Real.pi * (L.factorial : ℝ) ^ 4

theorem nestedInversePowerChain_exact_return (L : ℕ) :
    nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L) = 1 := by
  rw [nestedInversePowerChainEvolution_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, one_apply, ↓reduceIte]
    rcases exists_factorialFourth_mul_nestedChainEnergy x with ⟨N, hN⟩
    have hphase : nestedInversePowerReturnPeriod L * nestedInversePowerChainEnergy x =
        2 * Real.pi * N := by
      unfold nestedInversePowerReturnPeriod
      rw [mul_assoc, hN]
    have hphaseC : (nestedInversePowerReturnPeriod L : ℂ) *
        (nestedInversePowerChainEnergy x : ℂ) = ((2 * Real.pi * N : ℝ) : ℂ) := by
      exact_mod_cast hphase
    rw [hphaseC]
    convert Complex.exp_int_mul_two_pi_mul_I (-(N : ℤ)) using 1
    norm_num
    ring_nf
  · simp [Matrix.diagonal, hxy]

theorem nestedInversePowerChainEvolution_add (L : ℕ) (s t : ℝ) :
    nestedInversePowerChainEvolution L (s + t) =
      nestedInversePowerChainEvolution L s * nestedInversePowerChainEvolution L t := by
  rw [nestedInversePowerChainEvolution_diagonal, nestedInversePowerChainEvolution_diagonal,
    nestedInversePowerChainEvolution_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem nestedInversePowerChainEvolution_return_reflect (L : ℕ) (t : ℝ) :
    nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L - t) =
      (nestedInversePowerChainEvolution L t)ᴴ := by
  have hsplit := nestedInversePowerChainEvolution_add L
    (nestedInversePowerReturnPeriod L - t) t
  have hsum : nestedInversePowerReturnPeriod L - t + t =
      nestedInversePowerReturnPeriod L := by ring
  rw [hsum, nestedInversePowerChain_exact_return] at hsplit
  have hunit := nestedInversePowerChainEvolution_unitary L t
  have hright : nestedInversePowerChainEvolution L t *
      (nestedInversePowerChainEvolution L t)ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hunit
  calc
    nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L - t) =
        nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L - t) * 1 := by simp
    _ = nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L - t) *
        (nestedInversePowerChainEvolution L t *
          (nestedInversePowerChainEvolution L t)ᴴ) := by rw [hright]
    _ = (nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L - t) *
        nestedInversePowerChainEvolution L t) *
          (nestedInversePowerChainEvolution L t)ᴴ := by rw [Matrix.mul_assoc]
    _ = (nestedInversePowerChainEvolution L t)ᴴ := by rw [← hsplit]; simp

/-- Operator-norm two-qubit-gate complexity of the nested finite-volume evolution. -/
noncomputable def nestedOperatorTwoGateComplexity (L : ℕ) (ε t : ℝ) : ℕ∞ :=
  ⨅ c ∈ {c : List (LocalGate (PairQubit L)) | NestedOperatorApproximates t ε c},
    (twoGateCount c : ℕ∞)

theorem nestedOperatorTwoGateComplexity_le_of_circuit {L : ℕ} {ε t : ℝ}
    {c : List (LocalGate (PairQubit L))} (hc : NestedOperatorApproximates t ε c) :
    nestedOperatorTwoGateComplexity L ε t ≤ (twoGateCount c : ℕ∞) := by
  refine le_trans (iInf_le _ c) ?_
  exact iInf_le
    (fun _ : c ∈ {c : List (LocalGate (PairQubit L)) | NestedOperatorApproximates t ε c} =>
      (twoGateCount c : ℕ∞)) hc

theorem le_nestedOperatorTwoGateComplexity_iff {L : ℕ} (ε t : ℝ) (G : ℕ∞) :
    G ≤ nestedOperatorTwoGateComplexity L ε t ↔
      ∀ c : List (LocalGate (PairQubit L)),
        NestedOperatorApproximates t ε c → G ≤ (twoGateCount c : ℕ∞) := by
  rw [nestedOperatorTwoGateComplexity, le_iInf_iff]
  constructor
  · intro h c hc
    exact le_iInf_iff.mp (h c) hc
  · intro h c
    exact le_iInf fun hc => h c hc

theorem NestedOperatorApproximates.adjointCircuit_return_reflect {L : ℕ} {ε t : ℝ}
    {c : List (LocalGate (PairQubit L))} (hc : NestedOperatorApproximates t ε c) :
    NestedOperatorApproximates (nestedInversePowerReturnPeriod L - t) ε
      (adjointCircuit c) := by
  unfold NestedOperatorApproximates at hc ⊢
  rw [circuitMatrix_adjointCircuit, nestedInversePowerChainEvolution_return_reflect]
  calc
    ‖(circuitMatrix c)ᴴ - (nestedInversePowerChainEvolution L t)ᴴ‖ =
        ‖(circuitMatrix c - nestedInversePowerChainEvolution L t)ᴴ‖ := by
          rw [Matrix.conjTranspose_sub]
    _ = ‖circuitMatrix c - nestedInversePowerChainEvolution L t‖ :=
      Matrix.l2_opNorm_conjTranspose _
    _ ≤ ε := hc

theorem nestedOperatorTwoGateComplexity_exact_return_reflect (L : ℕ) (ε t : ℝ) :
    nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) =
      nestedOperatorTwoGateComplexity L ε t := by
  apply le_antisymm
  · rw [le_nestedOperatorTwoGateComplexity_iff]
    intro c hc
    have hadj := hc.adjointCircuit_return_reflect
    simpa using nestedOperatorTwoGateComplexity_le_of_circuit hadj
  · rw [le_nestedOperatorTwoGateComplexity_iff]
    intro c hc
    have hadj := hc.adjointCircuit_return_reflect
    have htime : nestedInversePowerReturnPeriod L -
        (nestedInversePowerReturnPeriod L - t) = t := by ring
    rw [htime] at hadj
    simpa using nestedOperatorTwoGateComplexity_le_of_circuit hadj

theorem nestedOperatorComplexity_floor_twoCeil {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        nestedOperatorTwoGateComplexity L ε t ∧
      nestedOperatorTwoGateComplexity L ε t ≤
        ((2 * ⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) := by
  have hramp := nestedInversePowerChain_floor_linear_growth hε hεmax htMin htLab
  constructor
  · rw [le_nestedOperatorTwoGateComplexity_iff]
    intro c hc
    exact_mod_cast hramp.1 c hc
  · rcases hramp.2 with ⟨c, hcost, herr⟩
    have hc : NestedOperatorApproximates t ε c := le_of_lt herr
    have hle := nestedOperatorTwoGateComplexity_le_of_circuit hc
    rw [hcost] at hle
    exact le_trans hle (by exact_mod_cast (Nat.sub_le (2 * ⌈2 * t / ε⌉₊) 1))

/-- Capstone: one nested static nearest-neighbour path has a robust linear laboratory-time
complexity excursion, exact factorial-four return, and identical reflected bounds. -/
theorem nestedStaticLocal_thermodynamic_ramp_return_reflection {L : ℕ} {t ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L) = 1 ∧
      nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) =
        nestedOperatorTwoGateComplexity L ε t ∧
      ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        nestedOperatorTwoGateComplexity L ε t ∧
      nestedOperatorTwoGateComplexity L ε t ≤
        ((2 * ⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) ∧
      ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
        nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) ∧
      nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) ≤
        ((2 * ⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) := by
  have href := nestedOperatorTwoGateComplexity_exact_return_reflect L ε t
  have hb := nestedOperatorComplexity_floor_twoCeil hε hεmax htMin htLab
  refine ⟨nestedInversePowerChain_exact_return L, href, hb.1, hb.2, ?_, ?_⟩
  · rw [href]
    exact hb.1
  · rw [href]
    exact hb.2

/-! ## Bounded infinite-chain completion -/

theorem sum_range_shift_succ_eq_Ioc (K N : ℕ) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range N, f (n + K + 1) =
      ∑ n ∈ Finset.Ioc K (K + N), f n := by
  refine Finset.sum_bij (fun n _ => n + K + 1) ?_ ?_ ?_ ?_
  · intro n hn
    have hnN : n < N := Finset.mem_range.mp hn
    simp only [Finset.mem_Ioc]
    omega
  · intro i hi j hj hij
    omega
  · intro n hn
    have hnK : K < n := (Finset.mem_Ioc.mp hn).1
    have hnTop : n ≤ K + N := (Finset.mem_Ioc.mp hn).2
    refine ⟨n - K - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro n hn
    rfl

theorem summable_shifted_inv_sq (K : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + K + 1 : ℕ) : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (K + 1)).2 hbase
  simpa [Nat.add_assoc] using hshift

theorem summable_shifted_inv_fourth (K : ℕ) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + K + 1 : ℕ) : ℝ) ^ 4) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (K + 1)).2 hbase
  simpa [Nat.add_assoc] using hshift

theorem tsum_shifted_inv_sq_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' n : ℕ, (1 : ℝ) / ((n + K + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro N
    change (∑ i ∈ Finset.range N,
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (i + K + 1)) ≤ 1 / (K : ℝ)
    have hEq := sum_range_shift_succ_eq_Ioc K N
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
    rw [hEq]
    have htail := sum_inv_sq_Ioc_le K hK (K + N) (by omega)
    have hlast : 0 ≤ 1 / ((K + N : ℕ) : ℝ) := by positivity
    linarith

theorem tsum_shifted_inv_fourth_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' n : ℕ, (1 : ℝ) / ((n + K + 1 : ℕ) : ℝ) ^ 4 ≤
      1 / (K : ℝ) ^ 3 := by
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro N
    change (∑ i ∈ Finset.range N,
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (i + K + 1)) ≤ 1 / (K : ℝ) ^ 3
    have hEq := sum_range_shift_succ_eq_Ioc K N
      (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4)
    rw [hEq]
    have htail := sum_inv_fourth_Ioc_le K hK (K + N) (by omega)
    have hlast : 0 ≤ 1 / ((K + N : ℕ) : ℝ) ^ 3 := by positivity
    linarith

abbrev InfinitePairConfig := ℕ × Bool → Bool

noncomputable def nestedInfiniteMatchingTerm (x : InfinitePairConfig) (n : ℕ) : ℝ :=
  if x (n, false) = true ∧ x (n, true) = true then
    1 / (((n + 1 : ℕ) : ℝ) ^ 2) else 0

noncomputable def nestedInfiniteBridgeTerm (x : InfinitePairConfig) (n : ℕ) : ℝ :=
  if x (n, true) = true ∧ x (n + 1, false) = true then
    1 / (((n + 2 : ℕ) : ℝ) ^ 4) else 0

noncomputable def nestedInfiniteEnergy (x : InfinitePairConfig) : ℝ :=
  (∑' n : ℕ, nestedInfiniteMatchingTerm x n) +
    ∑' n : ℕ, nestedInfiniteBridgeTerm x n

noncomputable def nestedTruncatedEnergy (L : ℕ) (x : InfinitePairConfig) : ℝ :=
  (∑ n ∈ Finset.range L, nestedInfiniteMatchingTerm x n) +
    ∑ n ∈ Finset.range (L - 1), nestedInfiniteBridgeTerm x n

def restrictInfinitePairConfig (L : ℕ) (x : InfinitePairConfig) :
    Config (PairQubit L) := fun q => x (q.1.val, q.2)

theorem nestedFiniteEnergy_restriction (L : ℕ) (x : InfinitePairConfig) :
    nestedInversePowerChainEnergy (restrictInfinitePairConfig L x) =
      nestedTruncatedEnergy L x := by
  unfold nestedInversePowerChainEnergy inverseSquareMatchingEnergy
    nestedInverseFourthBridgeEnergy nestedTruncatedEnergy
  apply congrArg₂ (· + ·)
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [restrictInfinitePairConfig, nestedInfiniteMatchingTerm]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [restrictInfinitePairConfig, nestedInfiniteBridgeTerm]

theorem nestedInfiniteMatchingTerm_nonneg (x : InfinitePairConfig) (n : ℕ) :
    0 ≤ nestedInfiniteMatchingTerm x n := by
  unfold nestedInfiniteMatchingTerm
  split_ifs <;> positivity

theorem nestedInfiniteBridgeTerm_nonneg (x : InfinitePairConfig) (n : ℕ) :
    0 ≤ nestedInfiniteBridgeTerm x n := by
  unfold nestedInfiniteBridgeTerm
  split_ifs <;> positivity

theorem nestedInfiniteMatchingTerm_le (x : InfinitePairConfig) (n : ℕ) :
    nestedInfiniteMatchingTerm x n ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  unfold nestedInfiniteMatchingTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem nestedInfiniteBridgeTerm_le (x : InfinitePairConfig) (n : ℕ) :
    nestedInfiniteBridgeTerm x n ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ 4) := by
  unfold nestedInfiniteBridgeTerm
  split_ifs
  · exact le_rfl
  · positivity

theorem summable_nestedInfiniteMatchingTerm (x : InfinitePairConfig) :
    Summable (nestedInfiniteMatchingTerm x) := by
  apply Summable.of_nonneg_of_le (nestedInfiniteMatchingTerm_nonneg x)
    (nestedInfiniteMatchingTerm_le x)
  simpa using summable_shifted_inv_sq 0

theorem summable_nestedInfiniteBridgeTerm (x : InfinitePairConfig) :
    Summable (nestedInfiniteBridgeTerm x) := by
  apply Summable.of_nonneg_of_le (nestedInfiniteBridgeTerm_nonneg x)
    (nestedInfiniteBridgeTerm_le x)
  simpa [Nat.add_assoc] using summable_shifted_inv_fourth 1

theorem nestedInfiniteEnergy_nonneg_le_three (x : InfinitePairConfig) :
    0 ≤ nestedInfiniteEnergy x ∧ nestedInfiniteEnergy x ≤ 3 := by
  have hmSum := summable_nestedInfiniteMatchingTerm x
  have hbSum := summable_nestedInfiniteBridgeTerm x
  have hmMajor : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa using summable_shifted_inv_sq 0
  have hbMajor : Summable (fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 4)) := by
    simpa [Nat.add_assoc] using summable_shifted_inv_fourth 1
  have hmCompare : (∑' n, nestedInfiniteMatchingTerm x n) ≤
      ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) :=
    Summable.tsum_le_tsum (nestedInfiniteMatchingTerm_le x) hmSum hmMajor
  have hbCompare : (∑' n, nestedInfiniteBridgeTerm x n) ≤
      ∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 4) :=
    Summable.tsum_le_tsum (nestedInfiniteBridgeTerm_le x) hbSum hbMajor
  have hmDecomp := hmMajor.sum_add_tsum_nat_add 1
  have hmTail := tsum_shifted_inv_sq_le 1 (by norm_num)
  have hmTail' : (∑' i : ℕ, (1 : ℝ) / ((i : ℝ) + 2) ^ 2) ≤ 1 := by
    convert hmTail using 1 <;> norm_num [Nat.cast_add, add_assoc]
  have hmBound : (∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) ≤ 2 := by
    norm_num [Nat.add_assoc] at hmDecomp
    have hmBound' : (∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
      rw [← hmDecomp]
      simp only [one_div] at hmTail'
      linarith [hmTail']
    convert hmBound' using 1
    norm_num [Nat.cast_add]
  have hbBound : (∑' n : ℕ, (1 : ℝ) / (((n + 2 : ℕ) : ℝ) ^ 4)) ≤ 1 := by
    simpa [Nat.add_assoc] using tsum_shifted_inv_fourth_le 1 (by norm_num)
  have hm0 : 0 ≤ ∑' n, nestedInfiniteMatchingTerm x n :=
    tsum_nonneg (nestedInfiniteMatchingTerm_nonneg x)
  have hb0 : 0 ≤ ∑' n, nestedInfiniteBridgeTerm x n :=
    tsum_nonneg (nestedInfiniteBridgeTerm_nonneg x)
  unfold nestedInfiniteEnergy
  constructor <;> linarith

theorem nestedInfiniteEnergy_uniform_tail {L : ℕ} (hL : 1 ≤ L)
    (x : InfinitePairConfig) :
    0 ≤ nestedInfiniteEnergy x - nestedTruncatedEnergy L x ∧
      nestedInfiniteEnergy x - nestedTruncatedEnergy L x ≤
        1 / (L : ℝ) + 1 / (L : ℝ) ^ 3 := by
  let fm := nestedInfiniteMatchingTerm x
  let fb := nestedInfiniteBridgeTerm x
  have hsm : Summable fm := summable_nestedInfiniteMatchingTerm x
  have hsb : Summable fb := summable_nestedInfiniteBridgeTerm x
  have hmDecomp := hsm.sum_add_tsum_nat_add L
  have hbDecomp := hsb.sum_add_tsum_nat_add (L - 1)
  have hEq : nestedInfiniteEnergy x - nestedTruncatedEnergy L x =
      (∑' n : ℕ, fm (n + L)) + ∑' n : ℕ, fb (n + (L - 1)) := by
    unfold nestedInfiniteEnergy nestedTruncatedEnergy
    dsimp only [fm, fb] at hmDecomp hbDecomp ⊢
    linarith
  have hsmTail : Summable (fun n : ℕ => fm (n + L)) :=
    (summable_nat_add_iff L).2 hsm
  have hsbTail : Summable (fun n : ℕ => fb (n + (L - 1))) :=
    (summable_nat_add_iff (L - 1)).2 hsb
  have hmMajor := summable_shifted_inv_sq L
  have hbMajor := summable_shifted_inv_fourth L
  have hmPoint (n : ℕ) : fm (n + L) ≤
      1 / (((n + L + 1 : ℕ) : ℝ) ^ 2) := by
    exact nestedInfiniteMatchingTerm_le x (n + L)
  have hbPoint (n : ℕ) : fb (n + (L - 1)) ≤
      1 / (((n + L + 1 : ℕ) : ℝ) ^ 4) := by
    have hindex : n + (L - 1) + 2 = n + L + 1 := by omega
    simpa [fb, hindex] using nestedInfiniteBridgeTerm_le x (n + (L - 1))
  have hmLe : (∑' n : ℕ, fm (n + L)) ≤
      ∑' n : ℕ, (1 : ℝ) / (((n + L + 1 : ℕ) : ℝ) ^ 2) :=
    Summable.tsum_le_tsum hmPoint hsmTail hmMajor
  have hbLe : (∑' n : ℕ, fb (n + (L - 1))) ≤
      ∑' n : ℕ, (1 : ℝ) / (((n + L + 1 : ℕ) : ℝ) ^ 4) :=
    Summable.tsum_le_tsum hbPoint hsbTail hbMajor
  have hmBound := tsum_shifted_inv_sq_le L hL
  have hbBound := tsum_shifted_inv_fourth_le L hL
  have hm0 : 0 ≤ ∑' n : ℕ, fm (n + L) := by
    apply tsum_nonneg
    intro n
    exact nestedInfiniteMatchingTerm_nonneg x (n + L)
  have hb0 : 0 ≤ ∑' n : ℕ, fb (n + (L - 1)) := by
    apply tsum_nonneg
    intro n
    exact nestedInfiniteBridgeTerm_nonneg x (n + (L - 1))
  rw [hEq]
  constructor <;> linarith

theorem nestedTruncatedEnergy_tendsto (x : InfinitePairConfig) :
    Filter.Tendsto (fun L : ℕ => nestedTruncatedEnergy (L + 1) x)
      Filter.atTop (nhds (nestedInfiniteEnergy x)) := by
  have htail (L : ℕ) := nestedInfiniteEnergy_uniform_tail (L := L + 1) (by omega) x
  have hbound : Filter.Tendsto
      (fun L : ℕ => 1 / ((L + 1 : ℕ) : ℝ) + 1 / ((L + 1 : ℕ) : ℝ) ^ 3)
      Filter.atTop (nhds 0) := by
    have hInv : Filter.Tendsto (fun L : ℕ => (1 : ℝ) / (L + 1))
        Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hPow := hInv.pow 3
    convert hInv.add hPow using 1 <;> norm_num [one_div, inv_pow]
  have hdiff : Filter.Tendsto
      (fun L : ℕ => nestedInfiniteEnergy x - nestedTruncatedEnergy (L + 1) x)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun L => (htail L).1) (fun L => (htail L).2) hbound
  have hconst : Filter.Tendsto (fun _ : ℕ => nestedInfiniteEnergy x)
      Filter.atTop (nhds (nestedInfiniteEnergy x)) := tendsto_const_nhds
  have hrecover := hconst.sub hdiff
  convert hrecover using 1
  · funext L
    ring_nf
  · ring_nf

/-- Complete capstone: bounded thermodynamic completion and the finite-volume ramp--return law
hold simultaneously for the same nested static nearest-neighbour family. -/
theorem nestedStaticLocal_complete_thermodynamic_ramp_return_reflection
    {L : ℕ} {t ε : ℝ} (x : InfinitePairConfig) (hL : 1 ≤ L)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 100)
    (htMin : 1024 * Real.pi * ε ≤ t)
    (htLab : t ≤ ε * L / 2) :
    nestedInversePowerChainEnergy (restrictInfinitePairConfig L x) =
        nestedTruncatedEnergy L x ∧
      (0 ≤ nestedInfiniteEnergy x ∧ nestedInfiniteEnergy x ≤ 3) ∧
      (0 ≤ nestedInfiniteEnergy x - nestedTruncatedEnergy L x ∧
        nestedInfiniteEnergy x - nestedTruncatedEnergy L x ≤
          1 / (L : ℝ) + 1 / (L : ℝ) ^ 3) ∧
      Filter.Tendsto (fun N : ℕ => nestedTruncatedEnergy (N + 1) x)
        Filter.atTop (nhds (nestedInfiniteEnergy x)) ∧
      (nestedInversePowerChainEvolution L (nestedInversePowerReturnPeriod L) = 1 ∧
        nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) =
          nestedOperatorTwoGateComplexity L ε t ∧
        ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
          nestedOperatorTwoGateComplexity L ε t ∧
        nestedOperatorTwoGateComplexity L ε t ≤
          ((2 * ⌈2 * t / ε⌉₊ : ℕ) : ℕ∞) ∧
        ((⌊t / (128 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
          nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) ∧
        nestedOperatorTwoGateComplexity L ε (nestedInversePowerReturnPeriod L - t) ≤
          ((2 * ⌈2 * t / ε⌉₊ : ℕ) : ℕ∞)) := by
  exact ⟨nestedFiniteEnergy_restriction L x,
    nestedInfiniteEnergy_nonneg_le_three x,
    nestedInfiniteEnergy_uniform_tail hL x,
    nestedTruncatedEnergy_tendsto x,
    nestedStaticLocal_thermodynamic_ramp_return_reflection hε hεmax htMin htLab⟩

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
