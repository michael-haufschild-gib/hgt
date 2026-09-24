import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantileParabolicNormalizedVarianceFlow
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarRelativeDisplacement
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePArithmeticVarianceNull
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePTerminalCentroidExcessSummability
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePIdealCentroidVarianceEscape

/-!
# Eventual local orientation of the literal Route-P cutoff flux

The exact one-atom normalized history flux is a signed matched-offset times
centered displacement, minus a displacement square. On the physical polar
scale, the matched offset tends to one and the centered displacement tends to
zero. Thus the square debt cannot reverse the signed local orientation at
late cutoffs. This is source-derived from the completed-node PNT estimate and
the actual matched/quantile centroid sums, not an imposed aperture or sign.

The theorem does not bound the cumulative signed flux, pay the global
centroid and square debts, or construct the meromorphic ordered-history graph.
-/

open Filter Topology
open scoped Chebyshev BigOperators

namespace RHTower
noncomputable section

def routePFlowScale (K : ℕ) : ℝ :=
  Real.exp (-Real.log ((K + 3 : ℕ) : ℝ) / 2)

private theorem routePFlowScale_pos (K : ℕ) : 0 < routePFlowScale K :=
  Real.exp_pos _

private theorem routePFlowScale_mul_exp (K : ℕ) :
    routePFlowScale K * Real.exp (Real.log ((K + 3 : ℕ) : ℝ) / 2) = 1 := by
  unfold routePFlowScale
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  ring

private theorem routePFlowScale_sq_mul (K : ℕ) :
    routePFlowScale K ^ (2 : ℕ) * ((K + 3 : ℕ) : ℝ) = 1 := by
  have hn : (0 : ℝ) < ((K + 3 : ℕ) : ℝ) := by positivity
  unfold routePFlowScale
  rw [show Real.exp (-Real.log ((K + 3 : ℕ) : ℝ) / 2) ^ (2 : ℕ) =
      Real.exp (-Real.log ((K + 3 : ℕ) : ℝ)) by
      calc
        Real.exp (-Real.log ((K + 3 : ℕ) : ℝ) / 2) ^ (2 : ℕ) =
            Real.exp (-Real.log ((K + 3 : ℕ) : ℝ) / 2) *
              Real.exp (-Real.log ((K + 3 : ℕ) : ℝ) / 2) := by ring
        _ = Real.exp (-Real.log ((K + 3 : ℕ) : ℝ)) := by
              rw [← Real.exp_add]
              congr 1
              ring]
  rw [Real.exp_neg, Real.exp_log hn]
  field_simp

private theorem tendsto_routePFlowScale_zero :
    Tendsto routePFlowScale atTop (𝓝 0) := by
  have hlog : Tendsto (fun K : ℕ => Real.log (((K + 3 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3))
  have hneg : Tendsto (fun K : ℕ =>
      -Real.log (((K + 3 : ℕ) : ℝ)) / 2) atTop atBot := by
    have hmul := hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
    convert tendsto_neg_atBot_iff.2 hmul using 1
    ext K
    ring
  exact Real.tendsto_exp_atBot.comp hneg

private theorem routeP_quantile_terminal (K : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (K + 3) =
      2 + ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  unfold ccmOutgoingPrimeCumulative ccmActualHeadParabolicMass
  rw [centroid_sum_range_shift_two criticalMellinAtomWeight hzero hone K]

private theorem routeP_quantile_next (K : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (K + 4) =
      2 + ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) := by
  have hq := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight (K + 3)
  rw [routeP_quantile_terminal K] at hq
  linarith

private theorem tendsto_routeP_scaled_node_error_zero :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadOutgoingNodeError (K + 3)) atTop (𝓝 0) := by
  simpa [routePFlowScale, Function.comp_def] using
    tendsto_scaled_ccmActualHeadOutgoingNodeError_atTop_zero.comp
      (tendsto_add_atTop_nat 3)

private theorem tendsto_routeP_scaled_displacement_zero :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadMatchedQuantilePolarDisplacement (K + 3)) atTop (𝓝 0) := by
  simpa [routePFlowScale, Function.comp_def] using
    tendsto_scaled_ccmActualHeadMatchedQuantilePolarDisplacement_atTop_zero.comp
      (tendsto_add_atTop_nat 3)

private theorem tendsto_routeP_scaled_atom_zero :
    Tendsto (fun K : ℕ => routePFlowScale K *
      criticalMellinAtomWeight (K + 3)) atTop (𝓝 0) := by
  have hw := tendsto_criticalMellinAtomWeight_zero.comp (tendsto_add_atTop_nat 3)
  simpa [Function.comp_def] using tendsto_routePFlowScale_zero.mul hw

theorem tendsto_routeP_scaled_mass_two :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadParabolicMass K) atTop (𝓝 2) := by
  have hsum := (((tendsto_routePFlowScale_zero.const_mul (2 : ℝ)).add
    tendsto_routeP_scaled_atom_zero).add
    tendsto_routeP_scaled_node_error_zero)
  have hmodel : Tendsto (fun K : ℕ =>
      2 * routePFlowScale K +
      routePFlowScale K * criticalMellinAtomWeight (K + 3) +
      routePFlowScale K * ccmActualHeadOutgoingNodeError (K + 3)) atTop (𝓝 0) := by
    simpa using hsum
  have heq (K : ℕ) :
      routePFlowScale K * ccmActualHeadParabolicMass K =
        2 - (2 * routePFlowScale K +
          routePFlowScale K * criticalMellinAtomWeight (K + 3) +
          routePFlowScale K * ccmActualHeadOutgoingNodeError (K + 3)) := by
    have hnode := two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError
      (K + 3) (by omega)
    rw [routeP_quantile_next] at hnode
    have hscale := routePFlowScale_mul_exp K
    have hsnode := congrArg (fun x : ℝ => routePFlowScale K * x) hnode
    nlinarith only [hsnode, hscale]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  convert (htwo.sub hmodel).congr'
    (Eventually.of_forall fun K => (heq K).symm)
    using 1 <;> norm_num

private theorem tendsto_routeP_scaled_psi_one :
    Tendsto (fun K : ℕ => routePFlowScale K ^ (2 : ℕ) *
      Chebyshev.psi ((K + 2 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have hratio : Tendsto (fun K : ℕ =>
      ((K + 1 : ℕ) : ℝ) / ((K + 3 : ℕ) : ℝ)) atTop (𝓝 1) := by
    have h := tendsto_add_mul_div_add_mul_atTop_nhds
      (1 : ℝ) 3 1 (show (1 : ℝ) ≠ 0 by norm_num)
    convert h using 1
    · ext K
      push_cast
      ring
    · norm_num
  have hprod := tendsto_routeP_psi_div_linear_one.mul hratio
  have heq (K : ℕ) :
      routePFlowScale K ^ (2 : ℕ) * Chebyshev.psi ((K + 2 : ℕ) : ℝ) =
        (Chebyshev.psi ((K + 2 : ℕ) : ℝ) / ((K + 1 : ℕ) : ℝ)) *
          (((K + 1 : ℕ) : ℝ) / ((K + 3 : ℕ) : ℝ)) := by
    have hk1 : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hk3 : ((K + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    have hs := routePFlowScale_sq_mul K
    field_simp [hk1, hk3]
    nlinarith only [hs]
  convert hprod.congr' (Eventually.of_forall fun K => (heq K).symm)
    using 1 <;> norm_num

private theorem tendsto_routeP_scaled_excess_zero :
    Tendsto (fun K : ℕ => routePFlowScale K ^ (2 : ℕ) *
      ccmActualHeadMatchedCentroidChebyshevExcess K) atTop (𝓝 0) := by
  have hs := tendsto_routePFlowScale_zero.pow 2
  have he := ccmActualHeadMatchedCentroidChebyshevExcess_tendsto
  simpa using hs.mul he

private theorem routeP_matched_mean_eq (K : ℕ) :
    ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid =
      (2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
        ccmActualHeadMatchedCentroidChebyshevExcess K) /
          ccmActualHeadParabolicMass K := by
  unfold ccmActualHeadParabolicCentroidMean
    ccmActualHeadMatchedCentroidChebyshevExcess
  ring

private theorem tendsto_routeP_scaled_matched_mean_one :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid)
        atTop (𝓝 1) := by
  have hnum : Tendsto (fun K : ℕ =>
      routePFlowScale K ^ (2 : ℕ) *
        (2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
          ccmActualHeadMatchedCentroidChebyshevExcess K)) atTop (𝓝 2) := by
    have h := (tendsto_routeP_scaled_psi_one.const_mul (2 : ℝ)).add
      tendsto_routeP_scaled_excess_zero
    convert h using 1
    · ext K
      ring
    · norm_num
  have hden := tendsto_routeP_scaled_mass_two
  have hdiv := hnum.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have heq (K : ℕ) :
      routePFlowScale K *
          ccmActualHeadParabolicCentroidMean K ccmActualHeadMatchedPolarCentroid =
        (routePFlowScale K ^ (2 : ℕ) *
          (2 * Chebyshev.psi ((K + 2 : ℕ) : ℝ) +
            ccmActualHeadMatchedCentroidChebyshevExcess K)) /
          (routePFlowScale K * ccmActualHeadParabolicMass K) := by
    rw [routeP_matched_mean_eq]
    have hm := (ccmActualHeadParabolicMass_pos K).ne'
    have hs := (routePFlowScale_pos K).ne'
    field_simp [hm, hs]
  convert hdiv.congr' (Eventually.of_forall fun K => (heq K).symm)
    using 1 <;> norm_num

private theorem routeP_quantile_first_sum (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      criticalMellinAtomWeight (n + 2) *
        ccmActualHeadQuantilePolarCentroid (n + 2)) =
      ccmActualHeadParabolicMass K ^ (2 : ℕ) / 2 +
        2 * ccmActualHeadParabolicMass K := by
  rw [← ccmActualHeadQuantileParabolicAggregate_one_eq_mass_sq_div_two_add_two_mul_mass]
  unfold ccmActualHeadQuantileParabolicAggregate
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change criticalMellinAtomWeight (n + 2) *
      ((ccmActualHeadQuantilePolarCoordinate (n + 2) +
        ccmActualHeadQuantilePolarCoordinate (n + 3)) / 2) =
      (ccmActualHeadQuantilePolarCoordinate (n + 3) ^ (2 : ℕ) -
        ccmActualHeadQuantilePolarCoordinate (n + 2) ^ (2 : ℕ)) / 2
  rw [← ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
  ring

private theorem routeP_quantile_mean_eq (K : ℕ) :
    ccmActualHeadParabolicCentroidMean K ccmActualHeadQuantilePolarCentroid =
      2 + ccmActualHeadParabolicMass K / 2 := by
  unfold ccmActualHeadParabolicCentroidMean
  rw [routeP_quantile_first_sum]
  have hm := (ccmActualHeadParabolicMass_pos K).ne'
  field_simp [hm]
  ring

private theorem tendsto_routeP_scaled_quantile_mean_one :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadParabolicCentroidMean K ccmActualHeadQuantilePolarCentroid)
        atTop (𝓝 1) := by
  have h := (tendsto_routePFlowScale_zero.const_mul (2 : ℝ)).add
    (tendsto_routeP_scaled_mass_two.mul_const (1 / 2 : ℝ))
  have heq (K : ℕ) :
      routePFlowScale K *
          ccmActualHeadParabolicCentroidMean K ccmActualHeadQuantilePolarCentroid =
        2 * routePFlowScale K +
          routePFlowScale K * ccmActualHeadParabolicMass K * (1 / 2 : ℝ) := by
    rw [routeP_quantile_mean_eq]
    ring
  convert h.congr' (Eventually.of_forall fun K => (heq K).symm) using 1
  norm_num

private theorem routeP_new_quantile_centroid_eq (K : ℕ) :
    ccmActualHeadQuantilePolarCentroid (K + 3) =
      2 + ccmActualHeadParabolicMass K +
        criticalMellinAtomWeight (K + 3) / 2 := by
  unfold ccmActualHeadQuantilePolarCentroid
  rw [routeP_quantile_terminal K, routeP_quantile_next K]
  ring

private theorem tendsto_routeP_scaled_matched_new_two :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadMatchedPolarCentroid (K + 3)) atTop (𝓝 2) := by
  have h := (((tendsto_routePFlowScale_zero.const_mul (2 : ℝ)).add
    tendsto_routeP_scaled_mass_two).add
    (tendsto_routeP_scaled_atom_zero.mul_const (1 / 2 : ℝ))).sub
      tendsto_routeP_scaled_displacement_zero
  have heq (K : ℕ) :
      routePFlowScale K * ccmActualHeadMatchedPolarCentroid (K + 3) =
        2 * routePFlowScale K +
          routePFlowScale K * ccmActualHeadParabolicMass K +
          routePFlowScale K * criticalMellinAtomWeight (K + 3) * (1 / 2 : ℝ) -
          routePFlowScale K * ccmActualHeadMatchedQuantilePolarDisplacement (K + 3) := by
    have hcent := ccmActualHeadQuantilePolarCentroid_eq_matched_add_displacement
      (K + 3)
    rw [routeP_new_quantile_centroid_eq] at hcent
    nlinarith only [congrArg (fun z : ℝ => routePFlowScale K * z) hcent]
  convert h.congr' (Eventually.of_forall fun K => (heq K).symm)
    using 1 <;> norm_num

theorem tendsto_routeP_scaled_centered_offset_one :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K)
      atTop (𝓝 1) := by
  convert tendsto_routeP_scaled_matched_new_two.sub
    tendsto_routeP_scaled_matched_mean_one using 1
  · ext K
    unfold ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset
    ring
  · norm_num

theorem tendsto_routeP_scaled_centered_displacement_zero :
    Tendsto (fun K : ℕ => routePFlowScale K *
      ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K)
      atTop (𝓝 0) := by
  have h := tendsto_routeP_scaled_displacement_zero.sub
    (tendsto_routeP_scaled_quantile_mean_one.sub
      tendsto_routeP_scaled_matched_mean_one)
  convert h using 1
  · ext K
    unfold ccmActualHeadMatchedQuantileParabolicCenteredDisplacement
    ring
  · norm_num

theorem routeP_eventually_positive_local_flux_orientation_factor :
    ∀ᶠ K : ℕ in atTop,
      0 < 2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K +
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K := by
  have h := (tendsto_routeP_scaled_centered_offset_one.const_mul (2 : ℝ)).add
    tendsto_routeP_scaled_centered_displacement_zero
  have hfactor : Tendsto (fun K : ℕ => routePFlowScale K *
      (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K +
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K))
      atTop (𝓝 2) := by
    convert h using 1
    · ext K
      ring
    · norm_num
  filter_upwards [hfactor.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2))]
    with K hK
  exact (mul_pos_iff_of_pos_left (routePFlowScale_pos K)).mp hK

theorem routeP_eventually_local_flux_opposes_centered_displacement :
    ∀ᶠ K : ℕ in atTop,
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K *
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K ≤ 0 := by
  filter_upwards [routeP_eventually_positive_local_flux_orientation_factor] with K hK
  rw [ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_centered_signed_increment]
  have hw : 0 ≤ criticalMellinAtomWeight (K + 3) :=
    criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _
  have hm : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hm' : 0 < ccmActualHeadParabolicMass (K + 1) :=
    ccmActualHeadParabolicMass_pos (K + 1)
  have hcoeff : 0 ≤ criticalMellinAtomWeight (K + 3) *
      ccmActualHeadParabolicMass K / ccmActualHeadParabolicMass (K + 1) := by
    positivity
  have hnonneg : 0 ≤
      (criticalMellinAtomWeight (K + 3) *
        ccmActualHeadParabolicMass K / ccmActualHeadParabolicMass (K + 1)) *
        (2 * ccmActualHeadMatchedQuantileParabolicCenteredMatchedOffset K +
          ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K) *
        ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hcoeff hK.le)
      (sq_nonneg (ccmActualHeadMatchedQuantileParabolicCenteredDisplacement K))
  nlinarith only [hnonneg]

end
end RHTower
