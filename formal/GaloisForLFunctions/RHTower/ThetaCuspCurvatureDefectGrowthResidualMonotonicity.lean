import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthPairRelativeCooling
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthLossCooling
/-!
# Strictly increasing weighted growth-transfer residual

The complete source residual, divided by the leading transfer coefficient
and multiplied by exp(8q), strictly increases on q >= 3/2. This follows
from the literal pair's relative cooling, the partition's strict decrease,
and support-gap decay of the deep and odd-sector losses. The theorem
contains no assumed residual sign; its center value remains decisive.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

open MeasureTheory Filter Set Topology

private def momentProductSlope (q : ℝ) (k j : ℕ) : ℝ :=
  -((k+1:ℕ):ℝ)*thetaCuspHigherLikelihoodSpectralMoment q 0^k*
    thetaCuspHigherLikelihoodSpectralMoment q 1*thetaCuspHigherLikelihoodSpectralMoment q j-
    thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*thetaCuspHigherLikelihoodSpectralMoment q (j+1)

private theorem hasDerivAt_expEight (q : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (8*t)) (8*Real.exp (8*q)) q := by
  have hi : HasDerivAt (fun t : ℝ => 8*t) 8 q := by
    simpa only [mul_one,one_mul,id_eq,mul_comm] using (hasDerivAt_id q).const_mul 8
  simpa only [mul_comm] using hi.exp

private def weightedMomentProduct (k j : ℕ) (q : ℝ) : ℝ :=
  Real.exp (8*q)*(thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*
    thetaCuspHigherLikelihoodSpectralMoment q j)

private theorem hasDerivAt_weightedMomentProduct {q : ℝ} (hq : 0 < q) (k j : ℕ) :
    HasDerivAt (weightedMomentProduct k j)
      (Real.exp (8*q)*(momentProductSlope q k j+
        8*(thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*
          thetaCuspHigherLikelihoodSpectralMoment q j))) q := by
  exact ((hasDerivAt_expEight q).mul (sourceMomentProduct_hasDerivAt hq k j)).congr_deriv
    (by unfold momentProductSlope; ring)

private theorem weightedMomentProduct_antitone (k j : ℕ) (hk : 1 ≤ k) :
    AntitoneOn (weightedMomentProduct k j) (Ici (3/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_weightedMomentProduct (by change 3/2 ≤ q at hq; linarith) k j).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    exact (hasDerivAt_weightedMomentProduct (by linarith) k j).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    have hq0 : 0 < q := by linarith
    rw [(hasDerivAt_weightedMomentProduct hq0 k j).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have h := sourceMomentProduct_cooling hq0 k j
    have hprod : 0 ≤ thetaCuspHigherLikelihoodSpectralMoment q 0^(k+1)*
        thetaCuspHigherLikelihoodSpectralMoment q j :=
      mul_nonneg (pow_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0) _)
        (thetaCuspHigherLikelihoodSpectralMoment_nonneg j)
    have hcoef : 8-3*((k+2:ℕ):ℝ) ≤ 0 := by
      have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
      push_cast
      linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hcoef hprod
    unfold momentProductSlope
    nlinarith

private def weightedDeepMoment (q : ℝ) : ℝ := Real.exp (8*q)*thetaCuspDeepTailMoment q 8

private theorem hasDerivAt_weightedDeepMoment {q : ℝ} (hq : 0 < q) :
    HasDerivAt weightedDeepMoment
      (Real.exp (8*q)*(8*thetaCuspDeepTailMoment q 8-thetaCuspDeepTailMoment q 9)) q := by
  exact ((hasDerivAt_expEight q).mul (hasDerivAt_thetaCuspDeepTailMoment 8 hq)).congr_deriv (by ring)

private theorem weightedDeepMoment_antitone : AntitoneOn weightedDeepMoment (Ici (3/2)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_weightedDeepMoment (by change 3/2 ≤ q at hq; linarith)).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    exact (hasDerivAt_weightedDeepMoment (by linarith)).differentiableAt.differentiableWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    have hq0 : 0 < q := by linarith
    rw [(hasDerivAt_weightedDeepMoment hq0).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (sub_nonpos.mpr (deepMoment_gap hq0 8))

private def weightedTransferLoss (q : ℝ) : ℝ :=
  weightedDeepMoment q+(3:ℝ)^7*weightedMomentProduct 1 8 q+
    (5:ℝ)^7*weightedMomentProduct 3 8 q+(7:ℝ)^7*weightedMomentProduct 5 8 q

private theorem weightedTransferLoss_antitone : AntitoneOn weightedTransferLoss (Ici (3/2)) := by
  intro x hx y hy hxy
  have hd := weightedDeepMoment_antitone hx hy hxy
  have h3 := mul_le_mul_of_nonneg_left (weightedMomentProduct_antitone 1 8 (by omega) hx hy hxy)
    (by positivity : (0:ℝ) ≤ 3^7)
  have h5 := mul_le_mul_of_nonneg_left (weightedMomentProduct_antitone 3 8 (by omega) hx hy hxy)
    (by positivity : (0:ℝ) ≤ 5^7)
  have h7 := mul_le_mul_of_nonneg_left (weightedMomentProduct_antitone 5 8 (by omega) hx hy hxy)
    (by positivity : (0:ℝ) ≤ 7^7)
  unfold weightedTransferLoss
  linarith

private theorem sourcePartition_strictAnti : StrictAntiOn thetaCuspLikelihoodPartition (Ici (3/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_thetaCuspLikelihoodPartition (by change 3/2 ≤ q at hq; linarith)).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    have hq0 : 0 < q := by linarith
    rw [(hasDerivAt_thetaCuspLikelihoodPartition hq0).deriv]
    exact neg_neg_of_pos (thetaCuspHigherLikelihoodSpectralMoment_one_pos hq0)

private def weightedPairReserve (q : ℝ) : ℝ :=
  (Real.exp (8*q)*dominantPairNormalizedTransfer q)/(2*thetaCuspLikelihoodPartition q^2)

private theorem weightedPairReserve_strictMono : StrictMonoOn weightedPairReserve (Ici (3/2)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by change 3/2 ≤ x at hx; linarith
  have hy0 : 0 < y := by change 3/2 ≤ y at hy; linarith
  have hPx := thetaCuspLikelihoodPartition_pos hx0
  have hPy := thetaCuspLikelihoodPartition_pos hy0
  have hP := sourcePartition_strictAnti hx hy hxy
  have hF := expEightDominantPair_strictMonoOn hx hy hxy
  have hFy : 0 < Real.exp (8*y)*dominantPairNormalizedTransfer y :=
    mul_pos (Real.exp_pos _) (div_pos (growthTransferFunctional_dominant_pair_pos hy)
      (growthTransferLeadingCoefficient_pos hy))
  unfold weightedPairReserve
  calc
    _ < (Real.exp (8*y)*dominantPairNormalizedTransfer y)/(2*thetaCuspLikelihoodPartition x^2) :=
      div_lt_div_of_pos_right hF (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left hFy.le (by positivity) (by nlinarith)

def weightedAbsorptionResidual (q : ℝ) : ℝ :=
  Real.exp (8*q)*transferAbsorptionResidual q/growthTransferLeadingCoefficient q

private theorem weightedAbsorptionResidual_eq {q : ℝ} (hq : 3/2 ≤ q) :
    weightedAbsorptionResidual q=weightedPairReserve q-weightedTransferLoss q := by
  have hc := growthTransferLeadingCoefficient_pos hq
  have hp := thetaCuspLikelihoodPartition_pos (show 0 < q by linarith)
  unfold weightedAbsorptionResidual transferAbsorptionResidual weightedPairReserve
    weightedTransferLoss weightedDeepMoment weightedMomentProduct dominantPairNormalizedTransfer
  field_simp [hc.ne',hp.ne']
  ring

theorem weightedAbsorptionResidual_strictMonoOn :
    StrictMonoOn weightedAbsorptionResidual (Ici (3/2)) := by
  intro x hx y hy hxy
  have hP := weightedPairReserve_strictMono hx hy hxy
  have hL := weightedTransferLoss_antitone hx hy hxy.le
  rw [weightedAbsorptionResidual_eq hx,weightedAbsorptionResidual_eq hy]
  linarith


end
end RHTower.ThetaCuspDefect
