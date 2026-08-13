import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexProjectiveWronskianRenewal
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceParabolicFloor

/-!
# Vacuum cancellation of shifted-Xi projective renewal curvature

The two weight-four contributions to characteristic-apex projective renewal curvature cancel at
the arcsine recession fixed point.  Consequently the full curvature is little-o of the literal
adaptive mixed arithmetic source action.  All asymptotic statements below are unconditional:
positivity needed for local identities is discharged eventually by shifted-Xi Hankel positivity.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open XiShiftedCanonicalAdmission

/-- Curvature source in the adjacent-degree projective-Wronskian renewal law. -/
def xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature (y : ℝ) (n : ℕ) : ℝ :=
  deriv (fun v => xiShiftedCanonicalAdmissionAdjacentEdge v (n + 1)) y *
      xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n +
    y⁻¹ ^ 2 + deriv (fun v => xiShiftedCanonicalAdmissionAlpha v (n + 1)) y

private theorem hasDerivAt_xiShiftedCanonicalAdmissionAdjacentEdge_succ
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    HasDerivAt
      (fun v => xiShiftedCanonicalAdmissionAdjacentEdge v (n + 1))
      (xiShiftedCanonicalAdmissionAdjacentEdge y (n + 1) *
        (xiShiftedCanonicalAdmissionEffectivityRate y n -
          xiShiftedCanonicalAdmissionEffectivityRate y (n + 1))) y := by
  have hHn : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hN := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
    hy hn hHn
  have hNnext := hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_neg_effectivityRate_mul
    hy (n := n + 1) (by omega) hH
  have hNpos : 0 < xiShiftedCanonicalAdmissionNorm y n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hHn]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hHn) (by omega)
  have hquot := hNnext.div hN hNpos.ne'
  rw [xiShiftedCanonicalAdmissionAdjacentEdge]
  simp only [Nat.add_sub_cancel]
  apply hquot.congr_deriv
  field_simp [hNpos.ne']
  ring

private theorem monicOrthoFirstCoeff_normalizedCentralBinom (n : ℕ) :
    HTGeometry.monicOrthoFirstCoeff
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n =
      -(n : ℝ) / 2 := by
  rw [HTGeometry.monicOrthoFirstCoeff_eq_neg_sum
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm]
  simp_rw [monicOrthoAlpha_normalizedCentralBinom]
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- Effective norm-decay rate has exact weight-two arcsine recession constant. -/
theorem tendsto_square_mul_xiShiftedCanonicalAdmissionEffectivityRate_succ (n : ℕ) :
    Tendsto
      (fun w : ℝ => w ^ 2 *
        xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) (n + 1))
      atTop (nhds ((4 * (n + 1 : ℕ) + 1 : ℕ) / 2 : ℝ)) := by
  let m := n + 1
  have hfirst := (tendsto_dimensionless_monicOrthoFirstCoeff m).const_mul (-2 : ℝ)
  have halpha := (tendsto_dimensionless_monicOrthoAlpha m).const_mul
    (2 * (m : ℝ) + 1)
  have hdim := hfirst.add halpha
  have hfirstArc := monicOrthoFirstCoeff_normalizedCentralBinom m
  rw [hfirstArc] at hdim
  have hlim : (-2 : ℝ) * (-(m : ℝ) / 2) +
      (2 * (m : ℝ) + 1) * (1 / 2 : ℝ) =
      ((4 * m + 1 : ℕ) / 2 : ℝ) := by
    push_cast
    ring
  rw [hlim] at hdim
  apply hdim.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (m + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (m + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (m + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hNfirst : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (m + 2)).PosDef :=
    XiShiftedCanonicalAdmission.momentHankel_posDef_of_le (by omega) hN'
  have hAfirst : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hfirstScale := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    hw m hNfirst hAfirst
  have halphaScale := normalizedAlpha_eq_square_mul_actualAlpha hw m hN' hA
  have hAm : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  rw [xiShiftedCanonicalAdmissionEffectivityRate,
    xiShiftedCanonicalAdmissionFirstCoeff_eq_monicOrthoFirstCoeff (by omega) hAm,
    xiShiftedCanonicalAdmissionAlpha_eq_monicOrthoAlpha hAm,
    hfirstScale, halphaScale]
  dsimp only [m]
  ring

/-- Motion of the adjacent Jacobi edge contributes the universal weight-six constant `-1/8`. -/
theorem tendsto_sixth_mul_deriv_xiShiftedCanonicalAdmissionAdjacentEdge_succ_succ
    (n : ℕ) :
    Tendsto
      (fun w : ℝ => w ^ 6 * deriv
        (fun y => xiShiftedCanonicalAdmissionAdjacentEdge y (n + 2)) (w ^ 2))
      atTop (nhds (-1 / 8 : ℝ)) := by
  let m := n + 1
  let b : ℝ → ℝ := fun w => w ^ 4 * HTGeometry.monicOrthoBeta
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 1)
  let e0 : ℝ → ℝ := fun w => w ^ 2 *
    xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) m
  let e1 : ℝ → ℝ := fun w => w ^ 2 *
    xiShiftedCanonicalAdmissionEffectivityRate (w ^ 2) (m + 1)
  have hb : Tendsto b atTop (nhds (1 / 16 : ℝ)) :=
    tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth (by omega)
  have he0 : Tendsto e0 atTop (nhds ((4 * m + 1 : ℕ) / 2 : ℝ)) := by
    simpa only [m] using
      tendsto_square_mul_xiShiftedCanonicalAdmissionEffectivityRate_succ n
  have he1 : Tendsto e1 atTop (nhds ((4 * (m + 1) + 1 : ℕ) / 2 : ℝ)) := by
    simpa only [m, Nat.add_assoc] using
      tendsto_square_mul_xiShiftedCanonicalAdmissionEffectivityRate_succ (n + 1)
  have hraw := hb.mul (he0.sub he1)
  have hlim : (1 / 16 : ℝ) *
      (((4 * m + 1 : ℕ) / 2 : ℝ) -
        ((4 * (m + 1) + 1 : ℕ) / 2 : ℝ)) = -1 / 8 := by
    push_cast
    ring
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (m + 4),
    eventually_gt_atTop (1 : ℝ)] with w hA hw
  have hAflow : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 3)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hB := hasDerivAt_xiShiftedCanonicalAdmissionAdjacentEdge_succ
    (sq_pos_of_pos (lt_trans zero_lt_one hw)) (n := m) (by omega) hAflow
  have hBval := xiShiftedCanonicalAdmissionAdjacentEdge_eq_monicOrthoBeta
    (n := m + 1) (by omega) hAflow
  change b w * (e0 w - e1 w) = w ^ 6 * deriv
    (fun y => xiShiftedCanonicalAdmissionAdjacentEdge y (m + 1)) (w ^ 2)
  rw [hB.deriv, hBval]
  simp only [b, e0, e1]
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  field_simp [hw0]

/-- Motion of the diagonal Jacobi coefficient has universal weight-four constant `-1/2`. -/
theorem tendsto_fourth_mul_deriv_xiShiftedCanonicalAdmissionAlpha_succ_succ
    (n : ℕ) :
    Tendsto
      (fun w : ℝ => w ^ 4 * deriv
        (fun y => xiShiftedCanonicalAdmissionAlpha y (n + 2)) (w ^ 2))
      atTop (nhds (-1 / 2 : ℝ)) := by
  let m := n + 1
  let b0 : ℝ → ℝ := fun w => w ^ 4 * HTGeometry.monicOrthoBeta
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 1)
  let b1 : ℝ → ℝ := fun w => w ^ 4 * HTGeometry.monicOrthoBeta
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 2)
  let a : ℝ → ℝ := fun w => w ^ 2 * HTGeometry.monicOrthoAlpha
    (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 1)
  have hb0 : Tendsto b0 atTop (nhds (1 / 16 : ℝ)) :=
    tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth (by omega)
  have hb1 : Tendsto b1 atTop (nhds (1 / 16 : ℝ)) :=
    tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth (by omega)
  have ha : Tendsto a atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_square_mul_xiShiftedActualMonicOrthoAlpha_half (m + 1)
  have hraw := (hb0.const_mul (2 * (m : ℝ))).sub
    ((hb1.const_mul (2 * ((m + 2 : ℕ) : ℝ))).add (ha.pow 2))
  have hlim : 2 * (m : ℝ) * (1 / 16 : ℝ) -
      (2 * ((m + 2 : ℕ) : ℝ) * (1 / 16 : ℝ) + (1 / 2 : ℝ) ^ 2) =
      -1 / 2 := by
    push_cast
    ring
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (m + 5),
    eventually_gt_atTop (1 : ℝ)] with w hA hw
  have hAflow : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) ((m + 1) + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hflow := hasDerivAt_xiShiftedCanonicalAdmissionAlpha_eq_adjacentJacobiFlow
    (sq_pos_of_pos (lt_trans zero_lt_one hw)) (n := m + 1) (by omega) hAflow
  change 2 * (m : ℝ) * b0 w -
      (2 * ((m + 2 : ℕ) : ℝ) * b1 w + a w ^ 2) =
    w ^ 4 * deriv
      (fun y => xiShiftedCanonicalAdmissionAlpha y (m + 1)) (w ^ 2)
  rw [hflow.deriv]
  simp only [b0, b1, a]
  push_cast
  ring

/-- The full projective-renewal curvature has vanishing weight-four recession limit. -/
theorem tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature_succ_zero
    (n : ℕ) :
    Tendsto (fun w : ℝ => w ^ 4 *
      xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature (w ^ 2) (n + 1))
      atTop (nhds 0) := by
  let m := n + 1
  let bd : ℝ → ℝ := fun w => w ^ 6 * deriv
    (fun y => xiShiftedCanonicalAdmissionAdjacentEdge y (m + 1)) (w ^ 2)
  let r : ℝ → ℝ := fun w =>
    xiShiftedCanonicalAdmissionApexProjectiveTopRatio (w ^ 2) m / w ^ 2
  let ad : ℝ → ℝ := fun w => w ^ 4 * deriv
    (fun y => xiShiftedCanonicalAdmissionAlpha y (m + 1)) (w ^ 2)
  have hbd : Tendsto bd atTop (nhds (-1 / 8 : ℝ)) := by
    simpa only [m] using
      tendsto_sixth_mul_deriv_xiShiftedCanonicalAdmissionAdjacentEdge_succ_succ n
  have hr : Tendsto r atTop (nhds 4) :=
    tendsto_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_div_square_four
      (by omega)
  have had : Tendsto ad atTop (nhds (-1 / 2 : ℝ)) := by
    simpa only [m] using
      tendsto_fourth_mul_deriv_xiShiftedCanonicalAdmissionAlpha_succ_succ n
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hraw := (hbd.mul hr).add (hone.add had)
  have hlim : (-1 / 8 : ℝ) * 4 + (1 + -1 / 2) = 0 := by norm_num
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  simp only [xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature, bd, r, ad, m]
  field_simp [hw0]
  ring

/-- Eventually, normalized projective-Wronskian renewal defect is exactly renewal curvature. -/
theorem eventually_xiShiftedCanonicalAdmissionApexProjectiveWronskian_renewalDefect_div_sq_eq_curvature
    (n : ℕ) :
    ∀ᶠ w : ℝ in atTop,
      (xiShiftedCanonicalAdmissionApexProjectiveWronskian (w ^ 2) (n + 2) -
          xiShiftedCanonicalAdmissionAdjacentEdge (w ^ 2) (n + 2) *
            xiShiftedCanonicalAdmissionApexProjectiveWronskian (w ^ 2) (n + 1)) /
          xiShiftedCanonicalAdmissionApexValue (w ^ 2) (n + 2) ^ 2 =
        xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature (w ^ 2) (n + 1) := by
  let m := n + 1
  have hQnext := tendsto_xiShiftedDimensionlessAdmission_eval_one
    (by omega : m + 1 ≠ 0)
  rw [xiShiftedArcsineAdmissionAmplitude_eval_one] at hQnext
  have hscaleNextNe : XiShiftedCanonicalAdmission.Arc.monicScale (m + 1) ≠ 0 := by
    unfold XiShiftedCanonicalAdmission.Arc.monicScale
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (m + 5),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (m + 5),
    eventually_gt_atTop (1 : ℝ), hQnext.eventually_ne hscaleNextNe]
      with w hN hA hw hQnextNe
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (m + 5)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hNnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : m + 1 ≤ m + 5) hN'
  have hAnext : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 1)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hsourceNext :=
    XiShiftedCanonicalAdmission.sourceCoordinateAdmission_eq_actualAdmission
      hw (by omega : 0 < m + 1) (ne_of_gt hNnext.det_pos) (ne_of_gt hAnext.det_pos)
  have hdenom : xiShiftedCanonicalAdmissionApexValue (w ^ 2) (m + 1) ≠ 0 := by
    rw [xiShiftedCanonicalAdmissionApexValue, ← hsourceNext,
      xiShiftedSourceCoordinateAdmission_eval_inv_square hw0]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hw0)) hQnextNe
  have hArenew : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (m + 4)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hrenew :=
    xiShiftedCanonicalAdmissionApexProjectiveWronskian_degreeRenewal
      (sq_pos_of_pos (lt_trans zero_lt_one hw)) (n := m) (by omega) hArenew
  change
    (xiShiftedCanonicalAdmissionApexProjectiveWronskian (w ^ 2) (m + 1) -
        xiShiftedCanonicalAdmissionAdjacentEdge (w ^ 2) (m + 1) *
          xiShiftedCanonicalAdmissionApexProjectiveWronskian (w ^ 2) m) /
        xiShiftedCanonicalAdmissionApexValue (w ^ 2) (m + 1) ^ 2 =
      xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature (w ^ 2) m
  rw [hrenew]
  unfold xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature
    xiShiftedCanonicalAdmissionApexProjectiveTopRatio
  field_simp [hdenom]
  ring

/-- Dimensionless cumulative Jacobi dissipation has exact arcsine recession constant. -/
theorem tendsto_dimensionlessCumulativeJacobiDissipation_succ (n : ℕ) :
    Tendsto
      (fun w : ℝ => dimensionlessCumulativeJacobiDissipation w (n + 1))
      atTop (nhds ((2 * (n + 1 : ℕ) + 1 : ℕ) / 2 : ℝ)) := by
  let m := n + 1
  let c : ℝ := 2 * (m : ℝ) + 1
  have hc : c ≠ 0 := by positivity
  have hsurplus := tendsto_dimensionlessProjectiveArithmeticSurplus
    (n := m) (by omega)
  have hflux := (tendsto_dimensionlessCumulativeJacobiFlux m).pow 2
  have hraw := (hsurplus.add hflux).div_const c
  have hlim :
      ((((2 * m + 1 : ℕ) : ℝ) ^ 2 / 4) +
          (((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2) / c =
        ((2 * m + 1 : ℕ) / 2 : ℝ) := by
    dsimp only [c]
    push_cast
    field_simp
    ring
  rw [hlim] at hraw
  apply hraw.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (m + 2),
    eventually_gt_atTop (1 : ℝ)] with w hN hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (m + 2)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hgap := dimensionlessProjectiveArithmeticSurplus_eq_cauchyGap
    hw (n := m) (by omega) hN'
  rw [hgap]
  dsimp only [c, m]
  field_simp
  ring

/-- Literal adaptive mixed source action has exact positive weight-four recession constant. -/
theorem tendsto_fourth_mul_xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_succ_succ
    (n : ℕ) :
    Tendsto
      (fun w : ℝ => w ^ 4 *
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 2))
      atTop (nhds ((2 * (n + 2 : ℕ) + 1 : ℕ) / 2 : ℝ)) := by
  let m := n + 2
  have hdim : Tendsto
      (fun w : ℝ => dimensionlessCumulativeJacobiDissipation w m)
      atTop (nhds ((2 * m + 1 : ℕ) / 2 : ℝ)) := by
    simpa only [m, Nat.add_assoc] using
      tendsto_dimensionlessCumulativeJacobiDissipation_succ (n + 1)
  apply hdim.congr'
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (m + 4),
    eventually_gt_atTop (1 : ℝ)] with w hA hw
  have hAsource : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (m + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hA
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      (by linarith : 1 / 2 < w) (n := m) (by omega) hAsource
  have hscale := dimensionlessCumulativeJacobiDissipation_eq_fourth_mul_actual
    hw (n := m) hA
  rw [hsource, hscale]

/-- Projective-renewal curvature is asymptotically negligible relative to literal source action. -/
theorem tendsto_xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature_div_adaptiveMixedCompletedSourceAction_zero
    (n : ℕ) :
    Tendsto
      (fun w : ℝ =>
        xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature (w ^ 2) (n + 1) /
        xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 2))
      atTop (nhds 0) := by
  have hcurv :=
    tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveRenewalCurvature_succ_zero n
  have hsource :=
    tendsto_fourth_mul_xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_succ_succ n
  have hsourceLim : ((2 * (n + 2 : ℕ) + 1 : ℕ) / 2 : ℝ) ≠ 0 := by positivity
  have hraw := hcurv.div hsource hsourceLim
  simp only [zero_div] at hraw
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  exact mul_div_mul_left _ _ (pow_ne_zero 4 hw0)

end
end RHTower
