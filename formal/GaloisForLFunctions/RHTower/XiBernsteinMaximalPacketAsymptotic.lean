import GaloisForLFunctions.RHTower.FiniteBernsteinCoordinatePacketAsymptotic
import GaloisForLFunctions.RHTower.XiBernsteinMaximalPacketGap

/-!
# Positive half-order asymptotic of the maximal Xi Bernstein packet

Under failure of RH, the endpoint-amplitude maximum is attained on a finite index packet.  Equal
normalized coordinates are aggregated before taking energy; their reciprocal-square weights add
and never cancel.  Distinct maximal coordinates have strictly gapped mixed moments, so the packet
has a positive sharp half-order limit.
-/

open Complex Filter Topology
open scoped BigOperators Real

namespace RHTower

noncomputable section

/-- Distinct normalized coordinates occurring in a finite Xi index packet. -/
def xiEndpointCoordinateSet (D : Finset XiZeroCopy) : Finset ℂ :=
  D.image xiEndpointNormalizedReciprocalSquare

/-- Aggregate reciprocal-square weight of one coordinate fibre in a finite Xi packet. -/
def xiEndpointCoordinateWeight (D : Finset XiZeroCopy) (u : ℂ) : ℂ :=
  finiteExponentialFiberCoefficient D xiZeroCopyReciprocalSquare
    xiEndpointNormalizedReciprocalSquare u

lemma xiEndpointCoordinateSet_nonempty
    {D : Finset XiZeroCopy} (hD : D.Nonempty) :
    (xiEndpointCoordinateSet D).Nonempty := by
  exact hD.image xiEndpointNormalizedReciprocalSquare

/-- Every occupied Xi coordinate fibre has nonzero aggregate reciprocal-square weight. -/
theorem xiEndpointCoordinateWeight_ne_zero
    {D : Finset XiZeroCopy} {u : ℂ}
    (hu : u ∈ xiEndpointCoordinateSet D) :
    xiEndpointCoordinateWeight D u ≠ 0 := by
  classical
  obtain ⟨q, hqD, hqu⟩ := Finset.mem_image.mp hu
  let F : Finset XiZeroCopy :=
    D.filter (fun r => xiEndpointNormalizedReciprocalSquare r = u)
  have hqF : q ∈ F := Finset.mem_filter.mpr ⟨hqD, hqu⟩
  have hconst : ∀ r ∈ F,
      xiZeroCopyReciprocalSquare r = xiZeroCopyReciprocalSquare q := by
    intro r hr
    have hru := (Finset.mem_filter.mp hr).2
    have heq : xiEndpointNormalizedReciprocalSquare r =
        xiEndpointNormalizedReciprocalSquare q := hru.trans hqu.symm
    dsimp only [xiEndpointNormalizedReciprocalSquare] at heq
    exact (div_left_inj'
      (Complex.ofReal_ne_zero.mpr primeArchEndpointHausdorffRadius_pos.ne')).mp heq
  have hcard : ((F.card : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨q, hqF⟩))
  have hq0 : xiZeroCopyReciprocalSquare q ≠ 0 := by
    rw [xiZeroCopyReciprocalSquare_eq]
    exact xiCentralReciprocalSquare_ne_zero q.1
  change (∑ r ∈ D with xiEndpointNormalizedReciprocalSquare r = u,
    xiZeroCopyReciprocalSquare r) ≠ 0
  change (∑ r ∈ F, xiZeroCopyReciprocalSquare r) ≠ 0
  rw [Finset.sum_eq_card_nsmul hconst, nsmul_eq_mul]
  exact mul_ne_zero hcard hq0

/-- **Positive half-order maximal Xi packet under failure of RH.**  The maximal endpoint
coordinates form a finite packet whose normalized energy has a strictly positive sharp
half-order limit. -/
theorem exists_positive_halfOrder_maximalXiBernsteinCoordinatePacket_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      Tendsto
        (fun n : ℕ => Real.sqrt n *
          finiteBernsteinCoordinatePacketEnergy
            (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) n /
              (B ^ 2) ^ n)
        atTop
        (nhds (∑ u ∈ xiEndpointCoordinateSet D,
          ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
            bernsteinAffineRowHalfOrderConstant u)) ∧
      0 < ∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant u := by
  classical
  obtain ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, hDsub⟩ :=
    exists_uniformlySeparated_maximal_xiEndpointAmplitudePacket_of_not_rh hRH
  let U : Finset ℂ := xiEndpointCoordinateSet D
  let C : ℂ → ℂ := xiEndpointCoordinateWeight D
  have hUne : U.Nonempty := xiEndpointCoordinateSet_nonempty hDne
  have hamp : ∀ u ∈ U, ‖u‖ + ‖1 - u‖ = B := by
    intro u hu
    obtain ⟨q, hqD, hqu⟩ := Finset.mem_image.mp hu
    rw [← hqu]
    simpa only [xiEndpointBernsteinAtomAmplitudeBase] using hD q hqD
  have hu0 : ∀ u ∈ U, u ≠ 0 := by
    intro u hu hu0
    have huB := hamp u hu
    rw [hu0] at huB
    norm_num at huB
    linarith
  have hu1 : ∀ u ∈ U, u ≠ 1 := by
    intro u hu hu1
    have huB := hamp u hu
    rw [hu1] at huB
    norm_num at huB
    linarith
  have hmixed : ∀ u ∈ U, ∀ v ∈ U, u ≠ v →
      ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < B ^ 2 ∧
        ∀ n : ℕ, ‖reflectedBernsteinCrossMoment u v n‖ ≤ gamma ^ n := by
    intro u hu v hv huv
    obtain ⟨q, hqD, hqu⟩ := Finset.mem_image.mp hu
    obtain ⟨r, hrD, hrv⟩ := Finset.mem_image.mp hv
    have hcoord : xiEndpointNormalizedReciprocalSquare q ≠
        xiEndpointNormalizedReciprocalSquare r := by
      rw [hqu, hrv]
      exact huv
    simpa only [hqu, hrv] using
      exists_uniform_mixedXiBernsteinCrossMoment_gap_of_distinct_maximal_coordinates
        hB (hD q hqD) (hD r hrD) hcoord
  have hlimit :=
    tendsto_sqrtNat_mul_finiteBernsteinCoordinatePacketEnergy_div_pow
      U C (lt_trans zero_lt_one hB) hamp hu0 hu1 hmixed
  have htermpos : ∀ u ∈ U,
      0 < ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u := by
    intro u hu
    exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr
      (xiEndpointCoordinateWeight_ne_zero hu)))
      (bernsteinAffineRowHalfOrderConstant_pos (hu0 u hu) (hu1 u hu))
  have hsumpos : 0 < ∑ u ∈ U,
      ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u := by
    apply Finset.sum_pos' (fun u hu => (htermpos u hu).le)
    obtain ⟨u, hu⟩ := hUne
    exact ⟨u, hu, htermpos u hu⟩
  exact ⟨D, B, beta, hB, hbeta1, hbeta, hDne, hD, hDsub,
    hlimit, hsumpos⟩

end

end RHTower
