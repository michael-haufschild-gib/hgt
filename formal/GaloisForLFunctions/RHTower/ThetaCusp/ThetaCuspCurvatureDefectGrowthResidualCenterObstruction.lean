import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthResidualMonotonicity
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Actual-center obstruction to the coarse growth-transfer residual

The explicit eighth-moment absorption residual is strictly negative at
the literal modular center. The dominant atom alone makes its coarse
cubic loss exceed the pair reserve at q = 5/3; strict monotonicity of the
weighted residual transports this sign to q = pi - 3/2.

This excludes that sufficient comparison, not the complete cumulant
transfer sign or RH. The positive survivors are the exact source residual
bound and its strict weighted monotonicity, with the literal pair cooling
strictly slower than the spectral losses.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section
open Set
/-- The pure second-atom cubic loss already exceeds this pair reserve. -/
private theorem dominantCubic_monomial_threshold :
    dominantPairPolynomial (5/3) <
      2*((5/3:ℝ)^10*growthCoefficient (5/3) 7*growthNumerator (5/3) 3)*
        (3:ℝ)^7*(1/4096)*bareMoment (5/3) 3 0^2*bareMoment (5/3) 3 8 := by
  rw [bareMoment_eq_polynomial (by norm_num : (5/3:ℝ)≠0),
    bareMoment_eq_polynomial (by norm_num : (5/3:ℝ)≠0)]
  norm_num [dominantPairPolynomial,anchorCoolingNumerator,binaryGrowthNumerator,
    binarySlopeNumerator,growthNumerator,slopeNumerator,growthCoefficient,growthCoefficientJet,
    coolingCoefficient,coolingCoefficientJet,coolingCoefficientJetTwo,binaryMoment,
    polynomialMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial]

private theorem dominantAtomScale_fiveThirds_gt :
    (1/4096:ℝ)<dominantAtomScale (5/3) := by
  have he1 : Real.exp 1 < (11/4:ℝ) := by linarith [Real.exp_one_lt_d9]
  have hpow : Real.exp 1^19 < (11/4:ℝ)^19 :=
    pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num)
  have he19 : Real.exp 19 < (16384:ℝ)^2 := by
    rw [show (19:ℝ)=(19:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
    exact hpow.trans (by norm_num)
  have hsquare : Real.exp (19/2)^2=Real.exp 19 := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  have he : Real.exp (19/2)<(16384:ℝ) := by nlinarith [Real.exp_pos (19/2)]
  have hprod : dominantAtomScale (5/3)*Real.exp (19/2)=4 := by
    unfold dominantAtomScale
    rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
    norm_num
  have hpos := dominantAtomScale_pos (5/3)
  nlinarith

theorem atomMoment_two_eq_scale {q : ℝ} (hq : 0 < q) (j : ℕ) :
    atomMoment 2 q j=dominantAtomScale q*bareMoment q 3 j := by
  have hg : thetaCuspLikelihoodGap 2=(3:ℝ) := by norm_num [thetaCuspLikelihoodGap]
  rw [atomMoment_eq_bare (by omega : 2 ≤ (2:ℕ)) hq,hg]
  unfold dominantAtomScale
  rw [show -(3/2)*(3:ℝ)=-(9/2) by ring,show -q*(3:ℝ)=-3*q by ring]
  ring

private theorem bareMoment_three_pos {q : ℝ} (hq : 0 < q) (j : ℕ) :
    0 < bareMoment q 3 j := by unfold bareMoment; positivity

private theorem dominantMoment_le_higher {q : ℝ} (hq : 0 < q) (j : ℕ) :
    dominantAtomScale q*bareMoment q 3 j ≤ thetaCuspHigherLikelihoodSpectralMoment q j := by
  have he : thetaCuspHigherLikelihoodSpectralMoment q j=
      atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq j
  rw [he,atomMoment_two_eq_scale hq]
  exact le_add_of_nonneg_right (thetaCuspDeepTailMoment_nonneg q j)

theorem transferAbsorptionResidual_le_dominant_cubic {q : ℝ} (hq : 3/2 ≤ q) :
    transferAbsorptionResidual q ≤ dominantPairTransfer q/2-
      growthTransferLeadingCoefficient q*(3:ℝ)^7*
        (dominantAtomScale q*bareMoment q 3 0)^2*(dominantAtomScale q*bareMoment q 3 8) := by
  have hq0 : 0 < q := by linarith
  have hc := growthTransferLeadingCoefficient_pos hq
  have hpair : 0 < dominantPairTransfer q := growthTransferFunctional_dominant_pair_pos hq
  have hp : 1 ≤ thetaCuspLikelihoodPartition q := by
    rw [thetaCuspLikelihoodPartition_eq_one_add_moment_zero hq0]
    linarith [thetaCuspHigherLikelihoodSpectralMoment_nonneg (B:=q) 0]
  have hb : dominantPairTransfer q/(2*thetaCuspLikelihoodPartition q^2) ≤ dominantPairTransfer q/2 :=
    div_le_div_of_nonneg_left hpair.le (by norm_num) (by nlinarith)
  have hm0 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B:=q) 0
  have hm8 := thetaCuspHigherLikelihoodSpectralMoment_nonneg (B:=q) 8
  have hd := thetaCuspDeepTailMoment_nonneg q 8
  have hmore : 0 ≤ ((5:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^4+
      (7:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^6)*
      thetaCuspHigherLikelihoodSpectralMoment q 8 := by positivity
  have htail : (3:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^2*
      thetaCuspHigherLikelihoodSpectralMoment q 8 ≤
      thetaCuspDeepTailMoment q 8+
        ((3:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^2+
         (5:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^4+
         (7:ℝ)^7*thetaCuspHigherLikelihoodSpectralMoment q 0^6)*
          thetaCuspHigherLikelihoodSpectralMoment q 8 := by nlinarith
  have ha0 : 0 < dominantAtomScale q*bareMoment q 3 0 :=
    mul_pos (dominantAtomScale_pos q) (bareMoment_three_pos hq0 0)
  have ha8 : 0 < dominantAtomScale q*bareMoment q 3 8 :=
    mul_pos (dominantAtomScale_pos q) (bareMoment_three_pos hq0 8)
  have hprod : (dominantAtomScale q*bareMoment q 3 0)^2*(dominantAtomScale q*bareMoment q 3 8) ≤
      thetaCuspHigherLikelihoodSpectralMoment q 0^2*thetaCuspHigherLikelihoodSpectralMoment q 8 := by
    gcongr
    · exact dominantMoment_le_higher hq0 0
    · exact dominantMoment_le_higher hq0 8
  unfold transferAbsorptionResidual
  have htail' := mul_le_mul_of_nonneg_left htail hc.le
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ growthTransferLeadingCoefficient q*(3:ℝ)^7)
  nlinarith

theorem transferAbsorptionResidual_fiveThirds_neg : transferAbsorptionResidual (5/3)<0 := by
  have hb := transferAbsorptionResidual_le_dominant_cubic (q:=5/3) (by norm_num)
  have ha := dominantAtomScale_fiveThirds_gt
  have ha0 := dominantAtomScale_pos (5/3)
  have hC := growthTransferLeadingCoefficient_pos (q:=5/3) (by norm_num)
  have hm0 := bareMoment_three_pos (q:=5/3) (by norm_num) 0
  have hm8 := bareMoment_three_pos (q:=5/3) (by norm_num) 8
  have hpoly := dominantCubic_monomial_threshold
  have hQ : (5/3:ℝ)^10*growthCoefficient (5/3) 7*growthNumerator (5/3) 3=
      (5/3:ℝ)^9*growthTransferLeadingCoefficient (5/3) := by
    unfold growthTransferLeadingCoefficient
    ring
  rw [hQ] at hpoly
  have hscale := mul_lt_mul_of_pos_left ha
    (by positivity : 0 < 2*(5/3:ℝ)^9*growthTransferLeadingCoefficient (5/3)*
      (3:ℝ)^7*bareMoment (5/3) 3 0^2*bareMoment (5/3) 3 8)
  have hstrong : dominantPairPolynomial (5/3) <
      2*(5/3:ℝ)^9*growthTransferLeadingCoefficient (5/3)*(3:ℝ)^7*
        dominantAtomScale (5/3)*bareMoment (5/3) 3 0^2*bareMoment (5/3) 3 8 := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hstrong (pow_pos ha0 2)
  rw [dominantPairTransfer_eq (by norm_num : (0:ℝ)<5/3)] at hb
  have hgoal : dominantAtomScale (5/3)^2*dominantPairPolynomial (5/3)/(5/3:ℝ)^9/2 <
      growthTransferLeadingCoefficient (5/3)*(3:ℝ)^7*
        (dominantAtomScale (5/3)*bareMoment (5/3) 3 0)^2*
          (dominantAtomScale (5/3)*bareMoment (5/3) 3 8) := by
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<(5/3:ℝ)^9)).mpr
    nlinarith only [hmul]
  linarith

theorem transferAbsorptionResidual_center_neg :
    transferAbsorptionResidual (thetaCuspLikelihoodCoordinate 0)<0 := by
  have hq : (3/2:ℝ)≤thetaCuspLikelihoodCoordinate 0 := by
    rw [thetaCuspLikelihoodCoordinate_zero_eq]
    linarith [Real.pi_gt_three]
  have hq5 : thetaCuspLikelihoodCoordinate 0<(5/3:ℝ) := by
    rw [thetaCuspLikelihoodCoordinate_zero_eq]
    linarith [Real.pi_lt_d2]
  have hm := weightedAbsorptionResidual_strictMonoOn hq (by norm_num : (3/2:ℝ)≤5/3) hq5
  have h5 : weightedAbsorptionResidual (5/3)<0 := by
    unfold weightedAbsorptionResidual
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _)
      transferAbsorptionResidual_fiveThirds_neg) (growthTransferLeadingCoefficient_pos (by norm_num))
  have hc := growthTransferLeadingCoefficient_pos hq
  have hw : weightedAbsorptionResidual (thetaCuspLikelihoodCoordinate 0)<0 := hm.trans h5
  unfold weightedAbsorptionResidual at hw
  by_contra h
  have hn : 0 ≤ transferAbsorptionResidual (thetaCuspLikelihoodCoordinate 0) := le_of_not_gt h
  have hp := div_nonneg (mul_nonneg (Real.exp_pos (8*thetaCuspLikelihoodCoordinate 0)).le hn) hc.le
  exact (not_lt_of_ge hp) hw

end
end RHTower.ThetaCuspDefect
