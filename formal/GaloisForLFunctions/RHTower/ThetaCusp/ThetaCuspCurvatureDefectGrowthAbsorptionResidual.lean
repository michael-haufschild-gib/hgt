import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthStableComponents
/-!
# Exact residual for complete curvature growth absorption

The complete cumulant transfer is bounded above by minus an explicit
residual of the literal dominant pair, stable eighth moment, and finite
odd-sector loss. Its positivity remains open. The pair contribution has
an exact rational polynomial form. A uniform factor-sixteen substitute
fails at q = 3/2; the full coordinate dependence must be retained.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

def dominantPairTransfer (q : ℝ) : ℝ :=
  growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 2)

def transferAbsorptionResidual (q : ℝ) : ℝ :=
  dominantPairTransfer q/(2*thetaCuspLikelihoodPartition q^2)-
    growthTransferLeadingCoefficient q*(thetaCuspDeepTailMoment q 8+
      ((3:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^2+
       (5:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^4+
       (7:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^6)*
        thetaCuspHigherLikelihoodSpectralMoment q 8)

theorem normalizedTransferWeight_pair_lower {q : ℝ} (hq : 0 < q) :
    1/(2*thetaCuspLikelihoodPartition q^2) ≤ normalizedTransferWeight q 2 := by
  have hp := thetaCuspLikelihoodPartition_pos hq
  have hm : 0 ≤ thetaCuspLikelihoodNormalizedMoment q 0 :=
    div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0) hp.le
  have hw : 420 ≤ finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 2 := by
    norm_num only [finiteLogWeight]
    have h : 0 ≤ 840*thetaCuspLikelihoodNormalizedMoment q 0+
      1260*thetaCuspLikelihoodNormalizedMoment q 0^2+
      1680*thetaCuspLikelihoodNormalizedMoment q 0^3+
      2100*thetaCuspLikelihoodNormalizedMoment q 0^4+
      2520*thetaCuspLikelihoodNormalizedMoment q 0^5+
      2940*thetaCuspLikelihoodNormalizedMoment q 0^6 := by positivity
    linarith
  unfold normalizedTransferWeight
  calc
    _ = 420*(thetaCuspLikelihoodPartition q)⁻¹^2/840 := by field_simp; norm_num
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hw (sq_nonneg _)) (by norm_num)

theorem sourceTransfer_le_neg_residual {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (likelihoodCumulantEight q) ≤ -transferAbsorptionResidual q := by
  have hq0 : 0 < q := by linarith
  have hmain := sourceTransfer_signed_upper hq
  have hsingle : normalizedTransferWeight q 1*rawTransferSector q 1 ≤
      growthTransferLeadingCoefficient q*thetaCuspDeepTailMoment q 8 := by
    unfold rawTransferSector
    rw [sourceTransfer_single_eq_deep hq0]
    have hw : normalizedTransferWeight q 1 ≤ 1 := by
      simpa using normalizedTransferWeight_le hq0 (k := 1) (by omega)
    exact (mul_le_of_le_one_left (deepTransfer_bounds hq).1 hw).trans (deepTransfer_bounds hq).2
  have hpair0 : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have hpair : dominantPairTransfer q/(2*thetaCuspLikelihoodPartition q^2) ≤
      normalizedTransferWeight q 2*rawTransferSector q 2 := by
    calc
      _ = (1/(2*thetaCuspLikelihoodPartition q^2))*dominantPairTransfer q := by ring
      _ ≤ normalizedTransferWeight q 2*dominantPairTransfer q :=
        mul_le_mul_of_nonneg_right (normalizedTransferWeight_pair_lower hq0) hpair0.le
      _ ≤ _ := mul_le_mul_of_nonneg_left (sourceTransfer_pair_dominant_le hq)
        (normalizedTransferWeight_pos hq0 (k := 2) (by omega)).le
  unfold transferAbsorptionResidual
  nlinarith

def dominantPairPolynomial (q : ℝ) : ℝ :=
  anchorCoolingNumerator q 3 3+2*polynomialMoment q 3 1*(growthNumerator q 3)^2

theorem growthTransferFunctional_bare_pair {q : ℝ} (hq : 0 < q) :
    growthTransferFunctional q (spectralPowerMoment (bareMoment q 3) 2)=dominantPairPolynomial q/q^9 := by
  rw [growthTransferFunctional_power_two]
  have hw : growthTransferFunctional q (momentConvolution (bareMoment q 3) (bareMoment q 3))=
      q^9*fullPairGrowthCooling q (bareMoment q 3) := by
    rw [growthTransferFunctional_eq,growthSlope_momentConvolution]
    unfold fullPairGrowthCooling fullPairGrowth
    rw [growthSlope_bare_polynomial hq.ne',growthFunctional_bare_polynomial hq.ne']
    field_simp [hq.ne']
  rw [hw,fullPairGrowthCooling_self_eq,selfGrowthCooling_bare_eq hq.ne',
    growthFunctional_bare_polynomial hq.ne',bareMoment_eq_polynomial hq.ne']
  unfold dominantPairPolynomial
  field_simp [hq.ne']
  ring

theorem dominantPairTransfer_eq {q : ℝ} (hq : 0 < q) :
    dominantPairTransfer q=(dominantAtomScale q)^2*dominantPairPolynomial q/q^9 := by
  have ham : atomMoment 2 q=(fun j => dominantAtomScale q*bareMoment q 3 j) := by
    funext j
    have hg : thetaCuspLikelihoodGap 2=(3:ℝ) := by norm_num [thetaCuspLikelihoodGap]
    rw [atomMoment_eq_bare (by omega : 2 ≤ (2:ℕ)) hq,hg]
    unfold dominantAtomScale
    rw [show -(3/2)*(3:ℝ)=-(9/2) by ring,show -q*(3:ℝ)=-3*q by ring]
    ring
  have hs : spectralPowerMoment (atomMoment 2 q) 2=
      fun j => dominantAtomScale q^2*spectralPowerMoment (bareMoment q 3) 2 j := by
    rw [ham]
    funext j
    exact spectralPowerMoment_smul _ _ _ _
  unfold dominantPairTransfer
  rw [hs,growthTransferFunctional_smul,growthTransferFunctional_bare_pair hq]
  ring

theorem dominantPairPolynomial_reserve_sixteen_fails :
    dominantPairPolynomial (3/2) <
      16*growthCoefficient (3/2) 7*growthNumerator (3/2) 3*
        polynomialMoment (3/2) 3 0*polynomialMoment (3/2) 3 8 := by
  norm_num [dominantPairPolynomial,anchorCoolingNumerator,binaryGrowthNumerator,
    binarySlopeNumerator,growthNumerator,slopeNumerator,growthCoefficient,growthCoefficientJet,
    coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo,binaryMoment,
    polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]

end
end RHTower.ThetaCuspDefect
