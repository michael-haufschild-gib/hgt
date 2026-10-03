import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDeepNextReserve
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPowerBudget
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedNextTransport
import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCalibration
/-! All deep source contributions are absorbed in the next transfer.
The complete source strictly dominates a residual involving only the
literal dominant cubic and even powers four, six, eight. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

theorem sourceCoordinate_actual_lower {x : ℝ} (hx : 0 ≤ x) :
    Real.pi-3/2 ≤ thetaCuspLikelihoodCoordinate x := by
  have he := Real.one_le_exp hx
  have he2 : 1 ≤ (Real.exp x)^2 := by nlinarith [Real.exp_pos x]
  have hp := le_mul_of_one_le_right Real.pi_pos.le he2
  unfold thetaCuspLikelihoodCoordinate
  linarith

theorem actualDeepMass_le {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) 0 ≤ (1/1000000:ℝ) := by
  have hq := sourceCoordinate_actual_lower hx
  have hdelta : (0:ℝ) ≤ thetaCuspLikelihoodCoordinate x-19/20 := by linarith [Real.pi_gt_three]
  have h := thetaCuspDeepTailMoment_le_eight_pow_mul_exp_support_comparison 0
    (by norm_num : (0:ℝ)<19/20) (by simpa using hdelta)
  have he : Real.exp (-(8*(thetaCuspLikelihoodCoordinate x-19/20))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hb := mul_le_mul_of_nonneg_right he (thetaCuspDeepTailMoment_nonneg (19/20) 0)
  norm_num only [pow_zero,one_mul] at h hb
  exact h.trans (hb.trans thetaCuspDeepTailMoment_calibration)

theorem deepPair_weighted_relative_absorption {x : ℝ} (hx : 0 ≤ x) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 2*
      pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (momentConvolution (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x))
          (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x))) ≤
      (16384/1000000)*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hqa : Real.pi-3/2 ≤ q := sourceCoordinate_actual_lower hx
  have hq : (3/2:ℝ) ≤ q := by linarith [Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have hC := pairRelativeLeadingCoefficient_pos hq
  have hD0 := thetaCuspDeepTailMoment_nonneg q 0
  have hD9 := thetaCuspDeepTailMoment_nonneg q 9
  have hF := deepTailPairRelativeTransfer_pos hq
  have hmass := actualDeepMass_le hx
  change thetaCuspDeepTailMoment q 0 ≤ (1/1000000:ℝ) at hmass
  have hupper := deepPairPairRelativeTransfer_upper hq
  have hlower := deepTailPairRelativeTransfer_lower hqa
  have hw0 := (normalizedTransferWeight_pos hq0 (k:=2) (by omega)).le
  have hw := normalizedTransferWeight_le hq0 (k:=2) (by omega)
  change normalizedTransferWeight q 2*_ ≤ (16384/1000000)*_
  calc
    _ ≤ normalizedTransferWeight q 2*(512*pairRelativeLeadingCoefficient q*thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q 9) :=
      mul_le_mul_of_nonneg_left hupper hw0
    _ ≤ (1/2)*(512*pairRelativeLeadingCoefficient q*thetaCuspDeepTailMoment q 0*thetaCuspDeepTailMoment q 9) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ 16384*thetaCuspDeepTailMoment q 0*pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) := by
      have h := mul_le_mul_of_nonneg_left hlower.le (show 0 ≤ 16384*thetaCuspDeepTailMoment q 0 by positivity)
      nlinarith only [h]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hmass (show 0 ≤ 16384*pairRelativeTransferFunctional q (thetaCuspDeepTailMoment q) by positivity)
      nlinarith only [h]
theorem mixedSector_weighted_deep_budget {x : ℝ} (hx : 0 ≤ x) {k : ℕ}
    (hk : 2 ≤ k ∧ k ≤ 8) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) k*
      (rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) k-
        pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
          (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) k)) ≤
      64*(k:ℝ)^9*thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0^(k-1)*
        pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
          (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hqa : Real.pi-3/2 ≤ q := sourceCoordinate_actual_lower hx
  have hq : (3/2:ℝ) ≤ q := by linarith [Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have hC := pairRelativeLeadingCoefficient_pos hq
  have hD := thetaCuspDeepTailMoment_nonneg q 9
  have hM := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B:=q) 0
  have hF := deepTailPairRelativeTransfer_pos hq
  have hb := sourceMixedPower_pairRelative_bounds hq hk.1
  have hm := mixedPowerMoment_marked_budget hq0 (by omega : 1 ≤ k) (by omega : 9 ≤ 9)
  have hh := hb.2.trans (mul_le_mul_of_nonneg_left hm hC.le)
  have hw := normalizedTransferWeight_le hq0 (k:=k) (by omega)
  have hw0 := (normalizedTransferWeight_pos hq0 (k:=k) (by omega)).le
  have hd := deepTailPairRelativeTransfer_lower hqa
  change normalizedTransferWeight q k*_ ≤ 64*(k:ℝ)^9*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*_
  calc
    _ ≤ normalizedTransferWeight q k*(pairRelativeLeadingCoefficient q*
        ((k:ℝ)^(9+1)*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*thetaCuspDeepTailMoment q 9)) :=
      mul_le_mul_of_nonneg_left hh hw0
    _ ≤ (1/(k:ℝ))*(pairRelativeLeadingCoefficient q*
        ((k:ℝ)^(9+1)*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*thetaCuspDeepTailMoment q 9)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (k:ℝ)^9*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1)*
        (pairRelativeLeadingCoefficient q*thetaCuspDeepTailMoment q 9) := by
      field_simp [hk0.ne']
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hd.le
        (show 0 ≤ 64*(k:ℝ)^9*thetaCuspHigherLikelihoodSpectralMoment q 0^(k-1) by positivity)
      nlinarith only [h]

theorem finiteLogWeight_lower {p : ℝ} (hp : 0 ≤ p) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    840/(k:ℝ) ≤ finiteLogWeight p k := by
  apply sub_nonneg.mp
  obtain ⟨hk1,hk8⟩ := hk
  interval_cases k <;> norm_num only [finiteLogWeight,Nat.cast_ofNat] <;> ring_nf <;> positivity

theorem normalizedTransferWeight_lower {q : ℝ} (hq : 0 < q) {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ 8) :
    (1/(k:ℝ))*(thetaCuspLikelihoodPartition q)⁻¹^k ≤ normalizedTransferWeight q k := by
  have hp := thetaCuspLikelihoodPartition_pos hq
  have hm : 0 ≤ thetaCuspLikelihoodNormalizedMoment q 0 :=
    div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0) hp.le
  have hw := finiteLogWeight_lower hm hk
  unfold normalizedTransferWeight
  calc
    _ = (840/(k:ℝ))*(thetaCuspLikelihoodPartition q)⁻¹^k/840 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw (pow_nonneg (inv_nonneg.mpr hp.le) k)) (by norm_num)

theorem actualSourceMass_lt {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspHigherLikelihoodSpectralMoment (thetaCuspLikelihoodCoordinate x) 0 < (1/399:ℝ) := by
  have h := three_hundred_ninety_nine_mul_thetaCuspHigherLikelihoodSpectralResponse_lt_one hx
  rw [←thetaCuspHigherLikelihoodSpectralMoment_zero_eq_response (thetaCuspLikelihoodCoordinate_pos hx)] at h
  linarith

theorem actualNormalizedTransferWeight_lower {x : ℝ} (hx : 0 ≤ x) {k : ℕ}
    (hk : 1 ≤ k ∧ k ≤ 8) :
    (399/400:ℝ)^k/(k:ℝ) ≤ normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) k := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq0 : 0 < q := thetaCuspLikelihoodCoordinate_pos hx
  have hp := thetaCuspLikelihoodPartition_pos hq0
  have hmass := actualSourceMass_lt hx
  change thetaCuspHigherLikelihoodSpectralMoment q 0 < (1/399:ℝ) at hmass
  have hpartition : thetaCuspLikelihoodPartition q < 400/399 := by
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hq0]
    linarith
  have hinv : (399/400:ℝ) ≤ (thetaCuspLikelihoodPartition q)⁻¹ := by
    rw [←one_div]
    exact (le_div_iff₀ hp).mpr (by linarith)
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 399/400) hinv k
  calc
    _ = (1/(k:ℝ))*(399/400:ℝ)^k := by ring
    _ ≤ (1/(k:ℝ))*(thetaCuspLikelihoodPartition q)⁻¹^k :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ _ := normalizedTransferWeight_lower hq0 hk

theorem mixedSector_weighted_deep_absorption {x : ℝ} (hx : 0 ≤ x) {k : ℕ}
    (hk : 2 ≤ k ∧ k ≤ 8) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) k*
      (rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) k-
        pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
          (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) k)) ≤
      (64*(k:ℝ)^9*(1/399:ℝ)^(k-1))*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x)) := by
  have hq : (3/2:ℝ) ≤ thetaCuspLikelihoodCoordinate x := by
    linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hF := (deepTailPairRelativeTransfer_pos hq).le
  have hM := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B:=thetaCuspLikelihoodCoordinate x) 0
  have hmass := (actualSourceMass_lt hx).le
  apply (mixedSector_weighted_deep_budget hx hk).trans
  gcongr

theorem completeDeep_even_absorption {x : ℝ} (hx : 0 ≤ x) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 2*rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) 2+
      normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 4*
        (rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) 4-
          pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
            (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 4))+
      normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 6*
        (rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) 6-
          pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
            (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 6))+
      normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 8*
        (rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) 8-
          pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
            (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 8)) <
      normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 1*rawPairRelativeSector (thetaCuspLikelihoodCoordinate x) 1 := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : (3/2:ℝ) ≤ q := by linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have hF := deepTailPairRelativeTransfer_pos hq
  have hpair := dominantDeepTail_weighted_relative_absorption hx
  have hdeep := deepPair_weighted_relative_absorption hx
  have h4 := mixedSector_weighted_deep_absorption hx (k:=4) (by omega)
  have h6 := mixedSector_weighted_deep_absorption hx (k:=6) (by omega)
  have h8 := mixedSector_weighted_deep_absorption hx (k:=8) (by omega)
  have hw := mul_le_mul_of_nonneg_right (actualNormalizedTransferWeight_lower hx (k:=1) (by omega)) hF.le
  rw [rawPairRelativeSector_two_split (thetaCuspLikelihoodCoordinate_pos hx),
    rawPairRelativeSector_one_deep (thetaCuspLikelihoodCoordinate_pos hx)]
  dsimp only [q] at hF hw
  norm_num only [Nat.reduceSub,pow_one,div_one] at hw h4 h6 h8
  nlinarith only [hpair,hdeep,h4,h6,h8,hw,hF]

def purePairRelativeResidual (q : ℝ) : ℝ :=
  normalizedTransferWeight q 3*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)-
    normalizedTransferWeight q 4*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 4)-
    normalizedTransferWeight q 6*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 6)-
    normalizedTransferWeight q 8*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 8)

theorem pairRelativeSourceTransfer_gt_pure_residual {x : ℝ} (hx : 0 ≤ x) :
    purePairRelativeResidual (thetaCuspLikelihoodCoordinate x) <
      pairRelativeSourceTransfer (thetaCuspLikelihoodCoordinate x) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : (3/2:ℝ) ≤ q := by linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have hdeep := completeDeep_even_absorption hx
  have h3 := mul_le_mul_of_nonneg_left
    (sub_nonneg.mp (sourceMixedPower_pairRelative_bounds hq (k:=3) (by omega)).1)
    (normalizedTransferWeight_pos hq0 (k:=3) (by omega)).le
  have h5 := mul_nonneg (normalizedTransferWeight_pos hq0 (k:=5) (by omega)).le
    (sourceConvolution_pairRelativeTransfer_nonneg hq (k:=5) (by omega))
  have h7 := mul_nonneg (normalizedTransferWeight_pos hq0 (k:=7) (by omega)).le
    (sourceConvolution_pairRelativeTransfer_nonneg hq (k:=7) (by omega))
  have hP := dominantPairPolynomial_pos hq
  have hC := growthTransferLeadingCoefficient_pos hq
  have hm := thetaCuspLikelihoodMean_pos hq0
  have hcorr : 0 ≤ 40320*q*dominantPairPolynomial q*growthTransferLeadingCoefficient q*thetaCuspLikelihoodMean q^9 := by positivity
  change purePairRelativeResidual q < pairRelativeSourceTransfer q
  change normalizedTransferWeight q 5*rawPairRelativeSector q 5 ≥ 0 at h5
  change normalizedTransferWeight q 7*rawPairRelativeSector q 7 ≥ 0 at h7
  change normalizedTransferWeight q 2*rawPairRelativeSector q 2+_+_+_ <
    normalizedTransferWeight q 1*rawPairRelativeSector q 1 at hdeep
  unfold purePairRelativeResidual pairRelativeSourceTransfer signedPairRelativeTransfer
  nlinarith only [hdeep,h3,h5,h7,hcorr]

end
end RHTower.ThetaCuspDefect
