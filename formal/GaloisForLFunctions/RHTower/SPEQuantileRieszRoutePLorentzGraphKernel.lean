import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzEdgeProducer
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCenteredBoundary
import GaloisForLFunctions.RHTower.SPEQuantileRieszParabolicBridge

/-!
# Exact active kernel of the P/SP-E Lorentz graph dissipation

The finite literal matched--quantile graph has a nonnegative coupled Lorentz dissipation.  This
module identifies its exact radical on the physical prime-power support: the only unpenalized
finite active profile is a common relative matched--quantile displacement.  Thus the source
graph is positive definite after quotienting by that one relative offset, while making no
cofinal resistance or completed-source estimate.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private theorem ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomWeight_half_add
    (n : ℕ) :
    ccmActualHeadQuantilePolarCentroid (n + 1) -
      ccmActualHeadQuantilePolarCentroid n =
        (criticalMellinAtomWeight n + criticalMellinAtomWeight (n + 1)) / 2 := by
  unfold ccmActualHeadQuantilePolarCentroid
  have h0 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have h1 := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (n + 1)
  linarith

private theorem ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow
    {m n : ℕ} (hmn : m < n) (hm : IsPrimePow m) :
    ccmActualHeadQuantilePolarCentroid m < ccmActualHeadQuantilePolarCentroid n := by
  have hstep : 0 < ccmActualHeadQuantilePolarCentroid (m + 1) -
      ccmActualHeadQuantilePolarCentroid m := by
    rw [ccmActualHeadQuantilePolarCentroid_succ_sub_eq_atomWeight_half_add]
    have hpos : 0 < criticalMellinAtomWeight m := criticalMellinAtomWeight_pos hm
    have hnonneg : 0 ≤ criticalMellinAtomWeight (m + 1) :=
      criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
    positivity
  have hmn' : m + 1 ≤ n := Nat.succ_le_iff.mpr hmn
  exact lt_of_lt_of_le (sub_pos.mp hstep)
    (ccmActualHeadQuantilePolarCentroid_le_of_le hmn')

/-- **Exact active radical classification.**  A finite literal Lorentz graph has zero
dissipation precisely when the matched--quantile displacement is constant on its active
prime-power vertices.  The remaining constant is a relative offset, not the common translation
gauge of the five-channel carrier. -/
theorem ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_eq_zero_iff_active_displacement_constant
    (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0 ↔
      ∀ m n : Fin (K + 1),
        IsPrimePow ((m : ℕ) + 2) → IsPrimePow ((n : ℕ) + 2) →
          ccmActualHeadMatchedQuantilePolarDisplacement ((m : ℕ) + 2) =
            ccmActualHeadMatchedQuantilePolarDisplacement ((n : ℕ) + 2) := by
  constructor
  · intro hzero m n hm hn
    by_cases hmn : m = n
    · simp [hmn]
    have hterm_nonneg (a b : ℕ) :
        0 ≤ -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue (a + 2) (b + 2) *
          (ccmActualHeadMatchedQuantilePolarDisplacement (b + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement (a + 2)) *
          (ccmActualHeadMatchedPolarCentroid (b + 2) -
            ccmActualHeadMatchedPolarCentroid (a + 2))) := by
      exact neg_nonneg.mpr
        (ccmActualHeadMatchedQuantileParabolicCrossKernelValue_mul_displacement_mul_centroid_nonpos a b)
    unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation at hzero
    have houter_zero : ∀ a ∈ Finset.range (K + 1),
        ∑ b ∈ (Finset.range (K + 1)).erase a,
          -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue (a + 2) (b + 2) *
            (ccmActualHeadMatchedQuantilePolarDisplacement (b + 2) -
              ccmActualHeadMatchedQuantilePolarDisplacement (a + 2)) *
            (ccmActualHeadMatchedPolarCentroid (b + 2) -
              ccmActualHeadMatchedPolarCentroid (a + 2))) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a ha =>
        Finset.sum_nonneg (fun b hb => hterm_nonneg a b))).mp hzero
    have hmrange : (m : ℕ) ∈ Finset.range (K + 1) := Finset.mem_range.mpr m.isLt
    have hnerase : (n : ℕ) ∈ (Finset.range (K + 1)).erase (m : ℕ) := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr n.isLt⟩
      exact fun h => hmn (Fin.ext h.symm)
    have htermzero :
        -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue ((m : ℕ) + 2) ((n : ℕ) + 2) *
          (ccmActualHeadMatchedQuantilePolarDisplacement ((n : ℕ) + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement ((m : ℕ) + 2)) *
          (ccmActualHeadMatchedPolarCentroid ((n : ℕ) + 2) -
            ccmActualHeadMatchedPolarCentroid ((m : ℕ) + 2))) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b hb => hterm_nonneg (m : ℕ) b)).mp
        (houter_zero (m : ℕ) hmrange) (n : ℕ) hnerase
    let c : ℝ := ccmActualHeadMatchedPolarCentroid ((n : ℕ) + 2) -
      ccmActualHeadMatchedPolarCentroid ((m : ℕ) + 2)
    let q : ℝ := ccmActualHeadQuantilePolarCentroid ((n : ℕ) + 2) -
      ccmActualHeadQuantilePolarCentroid ((m : ℕ) + 2)
    let d : ℝ := ccmActualHeadMatchedQuantilePolarDisplacement ((n : ℕ) + 2) -
      ccmActualHeadMatchedQuantilePolarDisplacement ((m : ℕ) + 2)
    have hcq : 0 < c * (c + q) := by
      rcases lt_or_gt_of_ne hmn with hlt | hgt
      · have hc : 0 < c := by
          dsimp [c]
          exact sub_pos.mpr
            (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (by omega))
        have hq : 0 < q := by
          dsimp [q]
          exact sub_pos.mpr
            (ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow
              (by omega) (by simpa using hm))
        positivity
      · have hc : c < 0 := by
          dsimp [c]
          exact sub_neg.mpr
            (strictMono_ccmActualHeadMatchedPolarCentroid_shift_two (by omega))
        have hq : q < 0 := by
          dsimp [q]
          exact sub_neg.mpr (ccmActualHeadQuantilePolarCentroid_lt_of_lt_of_isPrimePow
            (by omega) (by simpa using hn))
        nlinarith
    have hw : 0 <
        (criticalMellinAtomWeight ((m : ℕ) + 2) *
          criticalMellinAtomWeight ((n : ℕ) + 2)) / 2 := by
      have hwm : 0 < criticalMellinAtomWeight ((m : ℕ) + 2) :=
        criticalMellinAtomWeight_pos (by simpa using hm)
      have hwn : 0 < criticalMellinAtomWeight ((n : ℕ) + 2) :=
        criticalMellinAtomWeight_pos (by simpa using hn)
      exact div_pos (mul_pos hwm hwn) (by norm_num)
    have hfactor : 0 <
        (criticalMellinAtomWeight ((m : ℕ) + 2) *
          criticalMellinAtomWeight ((n : ℕ) + 2)) / 2 * (c * (c + q)) :=
      mul_pos hw hcq
    have hformula :
        -(ccmActualHeadMatchedQuantileParabolicCrossKernelValue ((m : ℕ) + 2) ((n : ℕ) + 2) *
          (ccmActualHeadMatchedQuantilePolarDisplacement ((n : ℕ) + 2) -
            ccmActualHeadMatchedQuantilePolarDisplacement ((m : ℕ) + 2)) *
          (ccmActualHeadMatchedPolarCentroid ((n : ℕ) + 2) -
            ccmActualHeadMatchedPolarCentroid ((m : ℕ) + 2))) =
          ((criticalMellinAtomWeight ((m : ℕ) + 2) *
            criticalMellinAtomWeight ((n : ℕ) + 2)) / 2 * (c * (c + q))) * d ^ (2 : ℕ) := by
      rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
      unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
      simp
      dsimp [c, q, d]
      rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement ((m : ℕ) + 2),
        ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement ((n : ℕ) + 2)]
      ring
    rw [hformula] at htermzero
    have hd2 : d ^ (2 : ℕ) = 0 := (mul_eq_zero.mp htermzero).resolve_left hfactor.ne'
    have hd : d = 0 := sq_eq_zero_iff.mp hd2
    dsimp [d] at hd
    linarith
  · intro hconstant
    unfold ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro n hn
    by_cases hmactive : IsPrimePow (m + 2)
    · by_cases hnactive : IsPrimePow (n + 2)
      · have hnrange : n ∈ Finset.range (K + 1) :=
          (Finset.mem_erase.mp hn).2
        have hd := hconstant ⟨m, Finset.mem_range.mp hm⟩
          ⟨n, Finset.mem_range.mp hnrange⟩ hmactive hnactive
        rw [hd]
        ring
      · have hweight : criticalMellinAtomWeight (n + 2) = 0 := by
          rw [criticalMellinAtomWeight_eq_div_sqrt,
            ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnactive, zero_div]
        rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge, hweight]
        ring
    · have hweight : criticalMellinAtomWeight (m + 2) = 0 := by
        rw [criticalMellinAtomWeight_eq_div_sqrt,
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hmactive, zero_div]
      rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge, hweight]
      ring

/-- The sole dissipation radical is invisible to every literal finite cross-cell source entry.
Thus the strict-cross source matrix itself descends through the relative-offset quotient. -/
theorem ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_zero_of_lorentzGraphDissipation_eq_zero
    {K : ℕ} (hzero : ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0)
    (m n : Fin (K + 1)) :
    ccmActualHeadMatchedQuantileParabolicCrossKernelValue ((m : ℕ) + 2) ((n : ℕ) + 2) = 0 := by
  by_cases hm : IsPrimePow ((m : ℕ) + 2)
  · by_cases hn : IsPrimePow ((n : ℕ) + 2)
    · have hd :=
        (ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_eq_zero_iff_active_displacement_constant K).mp
          hzero m n hm hn
      rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge]
      unfold ccmActualHeadMatchedQuantileLorentzSquare ccmActualHeadMatchedQuantileLorentzEdge
      simp
      rw [ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement ((m : ℕ) + 2),
        ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement ((n : ℕ) + 2), hd]
      ring_nf
      simp
    · have hweight : criticalMellinAtomWeight ((n : ℕ) + 2) = 0 := by
        rw [criticalMellinAtomWeight_eq_div_sqrt,
          ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]
      rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge, hweight]
      ring
  · have hweight : criticalMellinAtomWeight ((m : ℕ) + 2) = 0 := by
      rw [criticalMellinAtomWeight_eq_div_sqrt,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm, zero_div]
    rw [ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_lorentzEdge, hweight]
    ring

/-- The graph radical has a visible raw parabolic first mode: it is exactly the base relative
offset multiplied by the finite physical mass. -/
theorem ccmActualHeadMatchedQuantileParabolicCodiagonal_one_eq_neg_baseDisplacement_mul_mass_of_lorentzGraphDissipation_eq_zero
    {K : ℕ} (hzero : ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0) :
    ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 =
      -ccmActualHeadMatchedQuantilePolarDisplacement 2 * ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_one_eq_profile,
    ccmActualHeadMatchedPolarAdjacentCodiagonalProfile_massCoordinate]
  unfold ccmActualHeadParabolicMass
  rw [show -ccmActualHeadMatchedQuantilePolarDisplacement 2 *
      (∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2)) =
        -(ccmActualHeadMatchedQuantilePolarDisplacement 2 *
          ∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2)) by ring,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hactive : IsPrimePow (n + 2)
  · have hd :=
      (ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation_eq_zero_iff_active_displacement_constant K).mp
        hzero (0 : Fin (K + 1)) ⟨n, Finset.mem_range.mp hn⟩ Nat.prime_two.isPrimePow hactive
    simpa using congrArg (fun d : ℝ => d * criticalMellinAtomWeight (n + 2)) hd.symm
  · have hweight : criticalMellinAtomWeight (n + 2) = 0 := by
      rw [criticalMellinAtomWeight_eq_div_sqrt,
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hactive, zero_div]
    rw [hweight]
    ring

/-- The same radical is null for the canonical centered strict-cross producer.  Thus a terminal
readout, rather than the centered quadratic source, must detect any surviving relative offset. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredCharge_eq_zero_of_lorentzGraphDissipation_eq_zero
    {K : ℕ} (hzero : ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0) :
    ccmActualHeadMatchedQuantileParabolicCenteredCharge K = 0 := by
  have hpair : ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) = 0 := by
    rw [ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary_eq_strictCross]
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro n hn
    exact ccmActualHeadMatchedQuantileParabolicCrossKernelValue_eq_zero_of_lorentzGraphDissipation_eq_zero
      hzero ⟨m, Finset.mem_range.mp hm⟩ ⟨n, Finset.mem_range.mp (Finset.mem_erase.mp hn).2⟩
  have hcenter : ccmParabolicPairing
      (ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal K)
      (ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary K) = 0 := by
    rw [ccmActualHeadMatchedQuantileParabolicCenteredCodiagonal,
      ccmActualHeadMatchedQuantileParabolicCenteredSourceBoundary,
      ccmParabolicPairing_shift_same]
    exact hpair
  rw [ccmActualHeadMatchedQuantileParabolicCentered_pairing] at hcenter
  nlinarith [ccmActualHeadParabolicMass_pos K]

/-- On the exact finite graph radical, the finite Riesz parabolic readout is the base relative
offset times the physical mass and its remaining centered boundary coefficient.  This is a
finite-source identity only; it does not identify the independent terminal parabolic orbit with
the finite codiagonal. -/
theorem speQuantileRieszParabolicReadout_eq_neg_baseDisplacement_mul_mass_mul_terminalCoefficient_of_lorentzGraphDissipation_eq_zero
    (M : ℕ) {K : ℕ} (hzero : ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0) :
    speQuantileRieszParabolicReadout M (ccmActualHeadMatchedQuantileParabolicCodiagonal K) =
      -ccmActualHeadMatchedQuantilePolarDisplacement 2 * ccmActualHeadParabolicMass K *
        (Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K) := by
  have hone :=
    ccmActualHeadMatchedQuantileParabolicCodiagonal_one_eq_neg_baseDisplacement_mul_mass_of_lorentzGraphDissipation_eq_zero
      hzero
  have hcharge :=
    ccmActualHeadMatchedQuantileParabolicCenteredCharge_eq_zero_of_lorentzGraphDissipation_eq_zero
      hzero
  rw [ccmActualHeadMatchedQuantileParabolicCenteredCharge_eq] at hcharge
  have htwo : ccmActualHeadMatchedQuantileParabolicCodiagonal K 2 =
      -ccmActualHeadMatchedQuantileParabolicCenteredShift K *
        ccmActualHeadMatchedQuantileParabolicCodiagonal K 1 := by
    linarith
  unfold speQuantileRieszParabolicReadout
  rw [htwo, hone]
  ring

/-- Exact zero alternatives for the finite Riesz readout on the graph radical.  A nonzero
relative offset can survive it only at a zero of the centered boundary coefficient. -/
theorem speQuantileRieszParabolicReadout_eq_zero_iff_baseDisplacement_eq_zero_or_centeredCoefficient_eq_zero_of_lorentzGraphDissipation_eq_zero
    (M : ℕ) {K : ℕ} (hzero : ccmActualHeadMatchedQuantileParabolicLorentzGraphDissipation K = 0) :
    speQuantileRieszParabolicReadout M (ccmActualHeadMatchedQuantileParabolicCodiagonal K) = 0 ↔
      ccmActualHeadMatchedQuantilePolarDisplacement 2 = 0 ∨
        Real.sqrt (M : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K = 0 := by
  rw [speQuantileRieszParabolicReadout_eq_neg_baseDisplacement_mul_mass_mul_terminalCoefficient_of_lorentzGraphDissipation_eq_zero
    M hzero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hcoefficient
    · rcases mul_eq_zero.mp hleft with hdisplacement | hmass
      · exact Or.inl (neg_eq_zero.mp hdisplacement)
      · exact False.elim ((ccmActualHeadParabolicMass_pos K).ne' hmass)
    · exact Or.inr hcoefficient
  · rintro (hdisplacement | hcoefficient)
    · rw [hdisplacement]
      ring
    · rw [hcoefficient]
      ring

end RHTower
