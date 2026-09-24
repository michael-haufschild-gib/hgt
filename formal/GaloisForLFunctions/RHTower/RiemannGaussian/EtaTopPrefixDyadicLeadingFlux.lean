import GaloisForLFunctions.RHTower.RiemannGaussian.EtaTopPrefixDyadicEnergyWork
import GaloisForLFunctions.RHTower.RiemannGaussian.EtaEnergyLeadingFlux

/-!
# Sharp dyadic law for the isolated eta leading current

The finite arithmetic work block has a positive sharp limit at any
hypothetical right-half zero. The two non-leading currents have summable
endpoint-weighted absolute values. A general weighted-block lemma shows
their dyadic blocks vanish after the same normalization. Consequently the
single isolated head or adjacent-moment leading flux has the entire sharp
positive coefficient. This is a source-side obstruction theorem, not an
unconditional sign estimate excluding off-line zeros.
-/

open Filter Topology
namespace RiemannGaussian

/-- Endpoint-weighted absolute summability makes every dyadic block vanish
after scaling by any endpoint power at most one. -/
theorem tendsto_scaled_dyadic_block_of_weighted_summable
    (f : ℕ → ℝ) (q : ℝ) (hq : q ≤ 1)
    (hf : Summable (fun n : ℕ => ((2 * n + 1 : ℕ) : ℝ) * |f n|)) :
    Tendsto (fun N : ℕ =>
      (((2 * (N + 1) + 1 : ℕ) : ℝ) ^ q) *
        (∑ j ∈ Finset.range N, f (N + j))) atTop (nhds 0) := by
  let a (n : ℕ) : ℝ := ((2 * n + 1 : ℕ) : ℝ) * |f n|
  have ha : Summable a := hf
  have htail : Tendsto (fun N : ℕ => ∑' j : ℕ, a (N + j)) atTop (nhds 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (f := a)
  have hright : Tendsto (fun N : ℕ => 3 * (∑' j : ℕ, a (N + j)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul 3 htail
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun N => by
      let x : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
      have hx : 1 ≤ x := by dsimp [x]; norm_cast; omega
      have hscale : x ^ q ≤ x := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hx hq
      have hterm (j : ℕ) : x ^ q * |f (N + j)| ≤ 3 * a (N + j) := by
        have hweight : x ≤ 3 * (((2 * (N + j) + 1 : ℕ) : ℝ)) := by
          dsimp [x]
          push_cast
          nlinarith
        calc
          x ^ q * |f (N + j)| ≤
              (3 * (((2 * (N + j) + 1 : ℕ) : ℝ))) * |f (N + j)| :=
            mul_le_mul_of_nonneg_right (hscale.trans hweight) (abs_nonneg _)
          _ = 3 * a (N + j) := by dsimp [a]; ring
      have hshift : Summable (fun j : ℕ => a (N + j)) :=
        by simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 ha
      have hsum : (∑ j ∈ Finset.range N, a (N + j)) ≤
          ∑' j : ℕ, a (N + j) :=
        hshift.sum_le_tsum (Finset.range N) (fun j _ => by dsimp [a]; positivity)
      calc
        ‖x ^ q * ∑ j ∈ Finset.range N, f (N + j)‖ =
            x ^ q * |∑ j ∈ Finset.range N, f (N + j)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) q)]
        _ ≤ x ^ q * ∑ j ∈ Finset.range N, |f (N + j)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
            (Real.rpow_nonneg (by positivity) q)
        _ = ∑ j ∈ Finset.range N, x ^ q * |f (N + j)| := by
          rw [Finset.mul_sum]
        _ ≤ ∑ j ∈ Finset.range N, 3 * a (N + j) :=
          Finset.sum_le_sum (fun j _ => hterm j)
        _ = 3 * ∑ j ∈ Finset.range N, a (N + j) := by
          rw [Finset.mul_sum]
        _ ≤ 3 * ∑' j : ℕ, a (N + j) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
  · simpa only [Real.norm_eq_abs] using hright

open Complex
noncomputable section

private def rgEtaWorkCorrection (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference rho N +
    pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N

private theorem summable_oddEndpoint_mul_abs_rgEtaWorkCorrection
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) * |rgEtaWorkCorrection rho N|) := by
  have hinc := summable_oddEndpoint_mul_abs_topPrefixFiniteIncrementEnergyDifference rho
  have hrem := summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyRemainderFlux rho
  apply (hinc.add hrem).of_nonneg_of_le
  · intro N
    exact mul_nonneg (by positivity) (abs_nonneg _)
  · intro N
    dsimp only [rgEtaWorkCorrection]
    calc
      ((2 * N + 1 : ℕ) : ℝ) *
          |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference rho N +
            pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N| ≤
        ((2 * N + 1 : ℕ) : ℝ) *
          (|pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference rho N| +
            |pairedEtaTopPrefixFiniteEnergyRemainderFlux rho N|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
      _ = _ := by ring

private theorem rgEtaWork_eq_leadingFlux_add_correction
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork rho N =
      pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N + rgEtaWorkCorrection rho N := by
  rw [topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux,
    topPrefixFiniteEnergyFlux_eq_leading_add_remainder]
  unfold rgEtaWorkCorrection
  ring

/-- The isolated leading finite eta current carries the entire sharp
positive dyadic-block coefficient at every hypothetical right-half zero. -/
theorem tendsto_scaled_rgEtaDyadicLeadingFluxBlock_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) *
        (∑ j ∈ Finset.range N,
          pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j)))
      atTop
      (nhds ((1 - (1 / 2 : ℝ) ^ (2 * rgEtaPartnerExponent rho)) *
        (rgEtaSharpConstant rho) ^ 2)) := by
  have hq : 2 * rgEtaPartnerExponent rho ≤ 1 := by
    simp only [rgEtaPartnerExponent, NontrivialZetaZero.conjugatePartner_coe,
      Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hcorrection := tendsto_scaled_dyadic_block_of_weighted_summable
    (rgEtaWorkCorrection rho) (2 * rgEtaPartnerExponent rho) hq
    (summable_oddEndpoint_mul_abs_rgEtaWorkCorrection rho)
  have hwork := tendsto_scaled_rgEtaDyadicFiniteWorkBlock_of_half_lt_re rho hrho
  have hdiff := hwork.sub hcorrection
  simpa only [sub_zero] using hdiff.congr'
    (Eventually.of_forall fun N => by
      have hsum :
          (∑ j ∈ Finset.range N,
            pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
              rho (N + j)) =
          (∑ j ∈ Finset.range N,
            pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j)) +
          (∑ j ∈ Finset.range N, rgEtaWorkCorrection rho (N + j)) := by
        calc
          _ = ∑ j ∈ Finset.range N,
              (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j) +
                rgEtaWorkCorrection rho (N + j)) :=
            Finset.sum_congr rfl (fun j _ => rgEtaWork_eq_leadingFlux_add_correction rho (N + j))
          _ = _ := Finset.sum_add_distrib
      rw [hsum]
      dsimp only [rgEtaEndpoint]
      ring)

/-- At every hypothetical right-half zero, each sufficiently late dyadic
block of the isolated leading current is strictly positive. -/
theorem eventually_pos_rgEtaDyadicLeadingFluxBlock_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      0 < ∑ j ∈ Finset.range N,
        pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j) := by
  have hlim := tendsto_scaled_rgEtaDyadicLeadingFluxBlock_of_half_lt_re rho hrho
  have hpos := hlim.eventually
    (eventually_gt_nhds (rgEtaDyadicEnergyDropSharpLimit_pos rho))
  filter_upwards [hpos] with N hN
  have hscale : 0 < (rgEtaEndpoint N) ^ (2 * rgEtaPartnerExponent rho) :=
    Real.rpow_pos_of_pos (by unfold rgEtaEndpoint; positivity) _
  by_contra h
  have hnonpos : (∑ j ∈ Finset.range N,
      pairedEtaTopPrefixFiniteEnergyLeadingFlux rho (N + j)) ≤ 0 := le_of_not_gt h
  exact (not_le_of_gt hN) (mul_nonpos_of_nonneg_of_nonpos hscale.le hnonpos)

end
end RiemannGaussian
