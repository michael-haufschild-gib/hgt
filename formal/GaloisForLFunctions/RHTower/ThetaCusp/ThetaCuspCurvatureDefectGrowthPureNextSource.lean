import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthPureNextPolynomial
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthDeepSignedBudget
/-! Complete pair-relative source transfer is positive on the actual
theta ray. Literal pure cubic and quartic comparisons close the last
signed reserve after exact absorption of every deep sector. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
open Filter Set Topology
noncomputable section

theorem pairRelativeTransferFunctional_bare_three {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) 3)=pureCubicNextNumerator q/q^10 := by
  have h := hasDerivAt_transferFunctional_of_momentFlow
    (fun r => spectralPowerMoment (bareMoment r 3) 3) q (3*(3:ℝ))
    (fun j hj => hasDerivAt_barePowerMoment hq 3 3 hj)
  have hfrac := (hasDerivAt_dominantTriplePolynomial q).div (hasDerivAt_pow 10 q) (pow_ne_zero _ hq.ne')
  have he : (fun r => growthTransferFunctional r (spectralPowerMoment (bareMoment r 3) 3))=ᶠ[nhds q]
      (fun r => dominantTriplePolynomial r/r^10) := by
    filter_upwards [eventually_gt_nhds hq] with r hr
    exact growthTransferFunctional_bare_three hr
  have hd := h.unique (hfrac.congr_of_eventuallyEq he)
  simp only [Nat.reduceSub,Nat.cast_ofNat] at hd
  rw [growthTransferFunctional_bare_three hq] at hd
  rw [pairRelativeTransferFunctional_flow,growthTransferFunctional_bare_three hq]
  unfold pureCubicNextNumerator
  have ht : transferFlowFunctional q (spectralPowerMoment (bareMoment q 3) 3)=
      (q*dominantTriplePolynomialJet q-(10+9*q)*dominantTriplePolynomial q)/q^11 := by
    calc
      _ = (dominantTriplePolynomialJet q*q^10-dominantTriplePolynomial q*(10*q^9))/(q^10)^2-
          9*(dominantTriplePolynomial q/q^10) := by linarith only [hd]
      _ = _ := by field_simp [hq.ne']; ring
  rw [ht]
  field_simp [hq.ne']
  ring

theorem pairRelativeTransferFunctional_bare_four {q : ℝ} (hq : 0 < q) :
    pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) 4)=pureQuarticNextNumerator q/q^11 := by
  have h := hasDerivAt_transferFunctional_of_momentFlow
    (fun r => spectralPowerMoment (bareMoment r 3) 4) q (3*(4:ℝ))
    (fun j hj => hasDerivAt_barePowerMoment hq 3 4 hj)
  have hfrac := (hasDerivAt_dominantQuadruplePolynomial q).div (hasDerivAt_pow 11 q) (pow_ne_zero _ hq.ne')
  have he : (fun r => growthTransferFunctional r (spectralPowerMoment (bareMoment r 3) 4))=ᶠ[nhds q]
      (fun r => dominantQuadruplePolynomial r/r^11) := by
    filter_upwards [eventually_gt_nhds hq] with r hr
    exact growthTransferFunctional_bare_four hr
  have hd := h.unique (hfrac.congr_of_eventuallyEq he)
  simp only [Nat.reduceSub,Nat.cast_ofNat] at hd
  rw [growthTransferFunctional_bare_four hq] at hd
  rw [pairRelativeTransferFunctional_flow,growthTransferFunctional_bare_four hq]
  unfold pureQuarticNextNumerator
  have ht : transferFlowFunctional q (spectralPowerMoment (bareMoment q 3) 4)=
      (q*dominantQuadruplePolynomialJet q-(11+12*q)*dominantQuadruplePolynomial q)/q^12 := by
    calc
      _ = (dominantQuadruplePolynomialJet q*q^11-dominantQuadruplePolynomial q*(11*q^10))/(q^11)^2-
          12*(dominantQuadruplePolynomial q/q^11) := by linarith only [hd]
      _ = _ := by field_simp [hq.ne']; ring
  rw [ht]
  field_simp [hq.ne']
  ring

theorem bareCubic_pairRelative_lower {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeLeadingCoefficient q*bareMoment q 3 0^2*bareMoment q 3 9 <
      pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) 3) := by
  have hq0 : 0 < q := by linarith
  have h := div_lt_div_of_pos_right (pureCubicNext_reserve hq) (pow_pos hq0 10)
  rw [pairRelativeTransferFunctional_bare_three hq0,bareMoment_eq_polynomial hq0.ne',
    bareMoment_eq_polynomial hq0.ne']
  unfold pairRelativeLeadingCoefficient growthTransferLeadingCoefficient
  convert! h using 1
  norm_num only [Nat.reduceAdd]
  field_simp [hq0.ne']

theorem bareQuartic_pairRelative_absorption {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) 4) <
      256*bareMoment q 3 0*pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) 3) := by
  have hq0 : 0 < q := by linarith
  have h := div_lt_div_of_pos_right (pureQuarticNext_absorption hq) (pow_pos hq0 11)
  rw [pairRelativeTransferFunctional_bare_three hq0,pairRelativeTransferFunctional_bare_four hq0,
    bareMoment_eq_polynomial hq0.ne']
  convert! h using 1
  norm_num only [Nat.reduceAdd]
  field_simp [hq0.ne']

theorem pairRelativeTransferFunctional_dominant_power_eq {q : ℝ} (hq : 0 < q) (k : ℕ) :
    pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k)=
      dominantAtomScale q^k*pairRelativeTransferFunctional q (spectralPowerMoment (bareMoment q 3) k) := by
  have he : atomMoment 2 q=fun j => dominantAtomScale q*bareMoment q 3 j := by
    funext j
    exact atomMoment_two_eq_scale hq j
  have hs : spectralPowerMoment (fun j => dominantAtomScale q*bareMoment q 3 j) k=
      fun j => dominantAtomScale q^k*spectralPowerMoment (bareMoment q 3) k j := by
    funext j
    exact spectralPowerMoment_smul _ _ _ _
  rw [he,hs,pairRelativeTransferFunctional_smul]

theorem dominantCubic_pairRelative_lower {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeLeadingCoefficient q*atomMoment 2 q 0^2*atomMoment 2 q 9 <
      pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) := by
  have hq0 : 0 < q := by linarith
  have h := mul_lt_mul_of_pos_left (bareCubic_pairRelative_lower hq) (pow_pos (dominantAtomScale_pos q) 3)
  rw [pairRelativeTransferFunctional_dominant_power_eq hq0,atomMoment_two_eq_scale hq0 0,atomMoment_two_eq_scale hq0 9]
  convert! h using 1
  ring

theorem dominantQuartic_pairRelative_absorption {q : ℝ} (hq : 3/2 ≤ q) :
    pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 4) <
      256*atomMoment 2 q 0*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) := by
  have hq0 : 0 < q := by linarith
  have h := mul_lt_mul_of_pos_left (bareQuartic_pairRelative_absorption hq) (pow_pos (dominantAtomScale_pos q) 4)
  rw [pairRelativeTransferFunctional_dominant_power_eq hq0,pairRelativeTransferFunctional_dominant_power_eq hq0,
    atomMoment_two_eq_scale hq0 0]
  convert! h using 1
  ring

theorem dominantPower_pairRelative_le_cubic {q : ℝ} (hq : 3/2 ≤ q) {k : ℕ} (hk : 3 ≤ k) :
    pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) k) ≤
      (k:ℝ)^9*atomMoment 2 q 0^(k-3)*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) := by
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  apply (dominantPower_pairRelative_bounds hq hk).2.trans
  calc
    _ = ((k:ℝ)^9*atomMoment 2 q 0^(k-3))*(pairRelativeLeadingCoefficient q*atomMoment 2 q 0^2*atomMoment 2 q 9) := by
      rw [show k-1=(k-3)+2 by omega,pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dominantCubic_pairRelative_lower hq).le (by positivity)

theorem actualDominantMass_lt {x : ℝ} (hx : 0 ≤ x) :
    atomMoment 2 (thetaCuspLikelihoodCoordinate x) 0 < (1/399:ℝ) := by
  have hq0 := thetaCuspLikelihoodCoordinate_pos hx
  have hm := actualSourceMass_lt hx
  rw [fullMoment_eq_atom_add_deep hq0] at hm
  linarith [thetaCuspDeepTailMoment_nonneg (thetaCuspLikelihoodCoordinate x) 0]

theorem dominantHigher_weighted_pairRelative_absorption {x : ℝ} (hx : 0 ≤ x) {k : ℕ}
    (hk : 3 ≤ k ∧ k ≤ 8) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) k*
      pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) k) ≤
      ((k:ℝ)^8*(1/399:ℝ)^(k-3))*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 3) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : (3/2:ℝ) ≤ q := by linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have hk0 : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hF := (dominantPower_pairRelative_bounds hq (k:=3) (by omega)).1
  have hm := (actualDominantMass_lt hx).le
  change atomMoment 2 q 0 ≤ (1/399:ℝ) at hm
  have hw := normalizedTransferWeight_le hq0 (k:=k) (by omega)
  have hw0 := (normalizedTransferWeight_pos hq0 (k:=k) (by omega)).le
  change normalizedTransferWeight q k*_ ≤ ((k:ℝ)^8*(1/399:ℝ)^(k-3))*_
  calc
    _ ≤ normalizedTransferWeight q k*((k:ℝ)^9*atomMoment 2 q 0^(k-3)*
        pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)) :=
      mul_le_mul_of_nonneg_left (dominantPower_pairRelative_le_cubic hq hk.1) hw0
    _ ≤ (1/(k:ℝ))*((k:ℝ)^9*atomMoment 2 q 0^(k-3)*
        pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (k:ℝ)^8*atomMoment 2 q 0^(k-3)*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) := by
      field_simp [hk0.ne']
    _ ≤ _ := by gcongr

theorem dominantQuartic_weighted_pairRelative_absorption {x : ℝ} (hx : 0 ≤ x) :
    normalizedTransferWeight (thetaCuspLikelihoodCoordinate x) 4*
      pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 4) ≤
      (64/399)*pairRelativeTransferFunctional (thetaCuspLikelihoodCoordinate x)
        (spectralPowerMoment (atomMoment 2 (thetaCuspLikelihoodCoordinate x)) 3) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : (3/2:ℝ) ≤ q := by linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hq0 : 0 < q := by linarith
  have ha0 : 0 ≤ atomMoment 2 q 0 := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspSecondAtomMoment_nonneg q 0
  have hF := (dominantPower_pairRelative_bounds hq (k:=3) (by omega)).1
  have hm := (actualDominantMass_lt hx).le
  change atomMoment 2 q 0 ≤ (1/399:ℝ) at hm
  have hw := normalizedTransferWeight_le hq0 (k:=4) (by omega)
  have hw0 := (normalizedTransferWeight_pos hq0 (k:=4) (by omega)).le
  change normalizedTransferWeight q 4*_ ≤ (64/399)*_
  calc
    _ ≤ normalizedTransferWeight q 4*(256*atomMoment 2 q 0*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)) :=
      mul_le_mul_of_nonneg_left (dominantQuartic_pairRelative_absorption hq).le hw0
    _ ≤ (1/4)*(256*atomMoment 2 q 0*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3)) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hm (show 0 ≤ 64*pairRelativeTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 3) by positivity)
      nlinarith only [h]

theorem purePairRelativeResidual_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ purePairRelativeResidual (thetaCuspLikelihoodCoordinate x) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : (3/2:ℝ) ≤ q := by linarith [sourceCoordinate_actual_lower hx,Real.pi_gt_three]
  have hF := (dominantPower_pairRelative_bounds hq (k:=3) (by omega)).1
  have h4 := dominantQuartic_weighted_pairRelative_absorption hx
  have h6 := dominantHigher_weighted_pairRelative_absorption hx (k:=6) (by omega)
  have h8 := dominantHigher_weighted_pairRelative_absorption hx (k:=8) (by omega)
  have hw := mul_le_mul_of_nonneg_right (actualNormalizedTransferWeight_lower hx (k:=3) (by omega)) hF
  dsimp only [q] at hF hw
  unfold purePairRelativeResidual
  norm_num only [Nat.reduceSub] at h6 h8
  nlinarith only [h4,h6,h8,hw,hF]

theorem pairRelativeSourceTransfer_coordinate_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < pairRelativeSourceTransfer (thetaCuspLikelihoodCoordinate x) :=
  (purePairRelativeResidual_nonneg hx).trans_lt (pairRelativeSourceTransfer_gt_pure_residual hx)

end
end RHTower.ThetaCuspDefect
