import GaloisForLFunctions.HTGeometry.OffMatrixLift
import GaloisForLFunctions.HTGeometry.ThermodynamicMobileTailBounds
import GaloisForLFunctions.HTGeometry.TreePhaseTailCapacityLower

/-!
# Arbitrary-prefix invariance of the nested phase obstruction

The inverse-square phase block used by the static-local circuit lower bound lies strictly beyond a
mobile prefix.  An arbitrary unitary acting on that prefix can therefore be stripped after the
circuit-dependent untouched block is selected.  Operator-norm error is unchanged, separation
across the selected first-endpoint cut is preserved, and the original four-phase obstruction
applies verbatim.

This is the exact matrix-level statement that prevents early noncommuting dynamics from erasing
late phase-tail gate demand.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- A separated unitary cannot approximate the selected nested four-phase packet inside the
certified phase window. -/
theorem nestedInversePowerChain_no_separated_approximation
    {L K : ℕ} {W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {S : Finset (Fin L)} {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (hSblock : S ⊆ inverseSquareBlock hKL)
    (hphaseLo : 3 * Real.pi * ε ≤ ∑ j ∈ S, inverseSquarePhaseWeight t j)
    (hphaseHi : ∑ j ∈ S, inverseSquarePhaseWeight t j ≤ 5 * Real.pi * ε)
    (hsep : SeparatesAcross (firstEndpointSites S) W)
    (hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (hclose : ‖W - nestedInversePowerChainEvolution L t‖ ≤ ε) : False := by
  let x00 := pairFourConfig S false false
  let x01 := pairFourConfig S false true
  let x10 := pairFourConfig S true false
  let x11 := pairFourConfig S true true
  let U := nestedInversePowerChainEvolution L t
  let φ := t * nestedInversePowerChainEnergy x11
  have htpos : 0 < t := by
    have hKN : 0 < K := by omega
    have hp : 0 < 128 * Real.pi * ε * (K : ℝ) := by positivity
    exact lt_of_lt_of_le hp htlo
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [x00, x01, x10, x11]
    exact hsep.fourPoint_diagonal
  have hentry (x : Config (PairQubit L)) : ‖U x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - U) x x‖ ≤ ‖W - U‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - U) x x = W x x - U x x := rfl
    rw [hrewrite, norm_sub_rev] at hnorm
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

/-- **Arbitrary-prefix phase-tail lower law.**  If every circuit-dependent untouched phase block
admits a unitary prefix factor, that prefix cannot reduce the nested phase-tail gate demand. -/
theorem nestedInversePowerChain_twoGateCount_ge_of_prefixFactor
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    {T : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (hclose : ‖circuitMatrix c - T‖ ≤ ε)
    (hfactor : ∀ S : Finset (Fin L),
      S ⊆ inverseSquareBlock hKL →
      Disjoint S (circuitTouchedPairs c) →
      ∃ B : Matrix (Off (firstEndpointSites S)) (Off (firstEndpointSites S)) ℂ,
        B ∈ Matrix.unitaryGroup (Off (firstEndpointSites S)) ℂ ∧
        T = offMatrixLift (firstEndpointSites S) B *
          nestedInversePowerChainEvolution L t) :
    K ≤ twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c < K := Nat.lt_of_not_ge hnot
  rcases circuit_exists_inverseSquare_phase_subset c hK hKL hε htlo hthi hcost with
    ⟨S, hSblock, hSdisj, hphaseLo, hphaseHi⟩
  obtain ⟨B, hBunit, hT⟩ := hfactor S hSblock hSdisj
  let A := firstEndpointSites S
  let W := (offMatrixLift A B)ᴴ * circuitMatrix c
  have hsep : SeparatesAcross A W := by
    exact prefixStrip_separates A (circuitMatrix_separates_firstEndpoints c S hSdisj)
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
    have hLift := offMatrixLift_unitary A hBunit
    have hStar : (offMatrixLift A B)ᴴ ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Unitary.star_mem hLift
    exact mul_mem hStar (circuitMatrix_unitary c)
  have hstripTarget :
      (offMatrixLift A B)ᴴ * T = nestedInversePowerChainEvolution L t := by
    rw [hT]
    exact prefixStrip_mul_self A hBunit _
  have hstripClose : ‖W - nestedInversePowerChainEvolution L t‖ ≤ ε := by
    rw [← hstripTarget]
    change ‖(offMatrixLift A B)ᴴ * circuitMatrix c -
      (offMatrixLift A B)ᴴ * T‖ ≤ ε
    rw [prefixStrip_distance_eq A hBunit]
    exact hclose
  exact nestedInversePowerChain_no_separated_approximation
    hK hKL hε hεsmall htlo hthi hSblock hphaseLo hphaseHi hsep hWunit hstripClose

/-- Usable contradiction form of `twoGateCount_ge_of_mobilePrefix_fourPhaseWitness`: once the
combinatorial phase selector supplies an untouched `S`, the strict four-phase chord rules out the
purported approximation. -/
theorem false_of_mobilePrefix_fourPhaseWitness
    {L : ℕ} (c : List (LocalGate (PairQubit L)))
    {T : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {S : Finset (Fin L)} {ε : ℝ}
    (hSdisj : Disjoint S (circuitTouchedPairs c))
    (hclose : ‖circuitMatrix c - T‖ ≤ ε)
    {B : Matrix (Off (firstEndpointSites S)) (Off (firstEndpointSites S)) ℂ}
    {D : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hBunit : B ∈ Matrix.unitaryGroup (Off (firstEndpointSites S)) ℂ)
    (hT : T = offMatrixLift (firstEndpointSites S) B * D)
    (hDnorm : ∀ a b : Bool,
      ‖D (pairFourConfig S a b) (pairFourConfig S a b)‖ = 1)
    (hchord : 4 * ε < ‖
      D (pairFourConfig S false false) (pairFourConfig S false false) *
        D (pairFourConfig S true true) (pairFourConfig S true true) -
      D (pairFourConfig S false true) (pairFourConfig S false true) *
        D (pairFourConfig S true false) (pairFourConfig S true false)‖) : False := by
  let A := firstEndpointSites S
  let W := (offMatrixLift A B)ᴴ * circuitMatrix c
  have hsep : SeparatesAcross A W := by
    exact prefixStrip_separates A (circuitMatrix_separates_firstEndpoints c S hSdisj)
  have hLift := offMatrixLift_unitary A hBunit
  have hStar : (offMatrixLift A B)ᴴ ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hLift
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
    mul_mem hStar (circuitMatrix_unitary c)
  have hstripTarget : (offMatrixLift A B)ᴴ * T = D := by
    rw [hT]
    exact prefixStrip_mul_self A hBunit D
  have hstripClose : ‖W - D‖ ≤ ε := by
    rw [← hstripTarget]
    change ‖(offMatrixLift A B)ᴴ * circuitMatrix c -
      (offMatrixLift A B)ᴴ * T‖ ≤ ε
    rw [prefixStrip_distance_eq A hBunit]
    exact hclose
  let x00 := pairFourConfig S false false
  let x01 := pairFourConfig S false true
  let x10 := pairFourConfig S true false
  let x11 := pairFourConfig S true true
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [x00, x01, x10, x11]
    exact hsep.fourPoint_diagonal
  have hentry (x : Config (PairQubit L)) : ‖D x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - D) x x‖ ≤ ‖W - D‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - D) x x = W x x - D x x := rfl
    rw [hrewrite, norm_sub_rev] at hnorm
    exact le_trans hnorm hstripClose
  have hbound (x : Config (PairQubit L)) : ‖W x x‖ ≤ 1 :=
    entry_norm_bound_of_unitary hWunit _ _
  have hupp := norm_four_target_difference_le hfactor
    (hentry x00) (hentry x01) (hentry x10) (hentry x11)
    (hDnorm false false) (hDnorm true true)
    (hDnorm false true) (hDnorm true false)
    (hbound x01) (hbound x11)
  exact (not_lt_of_ge hupp) hchord

/-- Cut-oriented version of `false_of_mobilePrefix_fourPhaseWitness`.  Tree orientation may choose
an arbitrary sign field; only the physical circuit cut remains fixed. -/
theorem false_of_mobilePrefix_cutFourPhaseWitness
    {L : ℕ} (c : List (LocalGate (PairQubit L)))
    {T : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {S : Finset (Fin L)} {sigma : PairQubit L → Bool} {ε : ℝ}
    (hSdisj : Disjoint S (circuitTouchedPairs c))
    (hclose : ‖circuitMatrix c - T‖ ≤ ε)
    {B : Matrix (Off (firstEndpointSites S)) (Off (firstEndpointSites S)) ℂ}
    {D : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hBunit : B ∈ Matrix.unitaryGroup (Off (firstEndpointSites S)) ℂ)
    (hT : T = offMatrixLift (firstEndpointSites S) B * D)
    (hDnorm : ∀ a b : Bool,
      ‖D (cutFourConfig (firstEndpointSites S) sigma a b)
        (cutFourConfig (firstEndpointSites S) sigma a b)‖ = 1)
    (hchord : 4 * ε < ‖
      D (cutFourConfig (firstEndpointSites S) sigma false false)
          (cutFourConfig (firstEndpointSites S) sigma false false) *
        D (cutFourConfig (firstEndpointSites S) sigma true true)
          (cutFourConfig (firstEndpointSites S) sigma true true) -
      D (cutFourConfig (firstEndpointSites S) sigma false true)
          (cutFourConfig (firstEndpointSites S) sigma false true) *
        D (cutFourConfig (firstEndpointSites S) sigma true false)
          (cutFourConfig (firstEndpointSites S) sigma true false)‖) : False := by
  let A := firstEndpointSites S
  let W := (offMatrixLift A B)ᴴ * circuitMatrix c
  have hsep : SeparatesAcross A W := by
    exact prefixStrip_separates A (circuitMatrix_separates_firstEndpoints c S hSdisj)
  have hLift := offMatrixLift_unitary A hBunit
  have hStar : (offMatrixLift A B)ᴴ ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hLift
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
    mul_mem hStar (circuitMatrix_unitary c)
  have hstripTarget : (offMatrixLift A B)ᴴ * T = D := by
    rw [hT]
    exact prefixStrip_mul_self A hBunit D
  have hstripClose : ‖W - D‖ ≤ ε := by
    rw [← hstripTarget]
    change ‖(offMatrixLift A B)ᴴ * circuitMatrix c -
      (offMatrixLift A B)ᴴ * T‖ ≤ ε
    rw [prefixStrip_distance_eq A hBunit]
    exact hclose
  let x00 := cutFourConfig A sigma false false
  let x01 := cutFourConfig A sigma false true
  let x10 := cutFourConfig A sigma true false
  let x11 := cutFourConfig A sigma true true
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [x00, x01, x10, x11]
    exact hsep.fourPoint_diagonal_cut
  have hentry (x : Config (PairQubit L)) : ‖D x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - D) x x‖ ≤ ‖W - D‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - D) x x = W x x - D x x := rfl
    rw [hrewrite, norm_sub_rev] at hnorm
    exact le_trans hnorm hstripClose
  have hbound (x : Config (PairQubit L)) : ‖W x x‖ ≤ 1 :=
    entry_norm_bound_of_unitary hWunit _ _
  have hupp := norm_four_target_difference_le hfactor
    (hentry x00) (hentry x01) (hentry x10) (hentry x11)
    (hDnorm false false) (hDnorm true true)
    (hDnorm false true) (hDnorm true false)
    (hbound x01) (hbound x11)
  exact (not_lt_of_ge hupp) hchord

/-- **Abstract mobile-prefix phase-witness law.**  A circuit-dependent late four-phase witness is
enough: arbitrary unitary dynamics on the disjoint early prefix cancels with no error loss and no
gate charge.  The statement does not assume that the late diagonal factor is itself a circuit. -/
theorem twoGateCount_ge_of_mobilePrefix_fourPhaseWitness
    {L K : ℕ} (c : List (LocalGate (PairQubit L)))
    {T : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    {ε : ℝ}
    (hclose : ‖circuitMatrix c - T‖ ≤ ε)
    (hselect : twoGateCount c < K →
      ∃ S : Finset (Fin L), Disjoint S (circuitTouchedPairs c))
    (hwitness : ∀ S : Finset (Fin L),
      Disjoint S (circuitTouchedPairs c) →
      ∃ B : Matrix (Off (firstEndpointSites S)) (Off (firstEndpointSites S)) ℂ,
      ∃ D : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ,
        B ∈ Matrix.unitaryGroup (Off (firstEndpointSites S)) ℂ ∧
        T = offMatrixLift (firstEndpointSites S) B * D ∧
        (∀ a b : Bool, ‖D (pairFourConfig S a b) (pairFourConfig S a b)‖ = 1) ∧
        4 * ε < ‖
          D (pairFourConfig S false false) (pairFourConfig S false false) *
            D (pairFourConfig S true true) (pairFourConfig S true true) -
          D (pairFourConfig S false true) (pairFourConfig S false true) *
            D (pairFourConfig S true false) (pairFourConfig S true false)‖) :
    K ≤ twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c < K := Nat.lt_of_not_ge hnot
  obtain ⟨S, hSdisj⟩ := hselect hcost
  obtain ⟨B, D, hBunit, hT, hDnorm, hchord⟩ := hwitness S hSdisj
  exact false_of_mobilePrefix_fourPhaseWitness c hSdisj hclose
    hBunit hT hDnorm hchord

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
