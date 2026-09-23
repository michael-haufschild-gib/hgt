import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexContactOrientation
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalCurvatureRecession

/-!
# Shifted-Xi characteristic-apex projective phase reversal

Derives exact adjacent-degree Riccati transport for characteristic-apex values.  It
then proves two source-native far-right facts: the projective ratio has positive
limiting derivative, and its scaled Riccati discriminant tends to the strictly
positive value 2n + 9/4.  Together with negative derivative at every numerator
contact, this closes global decreasing-ratio strategies and identifies a genuine
projective phase reversal.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem xiShiftedCanonicalAdmissionApexProjectiveWronskian_eq_riccatiQuadratic
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    xiShiftedCanonicalAdmissionApexValue y (n + 1) * deriv
        (fun v => xiShiftedCanonicalAdmissionApexValue v n) y -
      xiShiftedCanonicalAdmissionApexValue y n * deriv
        (fun v => xiShiftedCanonicalAdmissionApexValue v (n + 1)) y =
      -2 * (n : ℝ) * xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ (2 : ℕ) +
        ((2 * (n : ℝ) + 1) / y - (2 * (n : ℝ) - 1) *
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n) *
          xiShiftedCanonicalAdmissionApexValue y n *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) -
        2 * ((n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *
          xiShiftedCanonicalAdmissionApexValue y n ^ (2 : ℕ) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix s ((n + 1) + 2)).PosDef := by
    simpa only [s, Nat.add_assoc] using hH
  have hPn : (HTGeometry.monicOrtho s n).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y n := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHn]
  have hPnext : (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext]
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hfirst := HTGeometry.monicOrthoFirstCoeff_succ_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 3)
  have hrecPoly := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n + 1) (by omega : n + 1 + 1 ≤ n + 3)
  have hrec := congrArg (fun p : Polynomial ℝ => p.eval y⁻¹) hrecPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at hrec
  simp only [s] at hPn hPnext
  rw [show n + 1 - 1 = n by omega, hPn, hPnext] at hrec
  have hAn := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    hy hn hHn
  have hAnext := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    (n := n + 1) hy (by omega) hH
  rw [hPnext] at hAn
  have hrec' :
      (HTGeometry.monicOrtho s (n + 2)).eval y⁻¹ =
        (y⁻¹ - HTGeometry.monicOrthoAlpha s (n + 1)) *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) -
        HTGeometry.monicOrthoBeta s (n + 1) *
          xiShiftedCanonicalAdmissionApexValue y n := by
    rw [show n + 2 = n + 1 + 1 by omega]
    linarith [hrec]
  simp only [s] at hrec'
  rw [hrec'] at hAnext
  rw [hAn.deriv, hAnext.deriv, hfirst]
  field_simp [ne_of_gt hy]
  push_cast
  ring


theorem hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_eq_riccati
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hdenom : xiShiftedCanonicalAdmissionApexValue y (n + 1) ≠ 0) :
    HasDerivAt (fun v => xiShiftedCanonicalAdmissionApexProjectiveTopRatio v n)
      (-2 * (n : ℝ) +
        ((2 * (n : ℝ) + 1) / y - (2 * (n : ℝ) - 1) *
          HTGeometry.monicOrthoAlpha
            (fun k => (xiShiftedReciprocalMoment y k).re) n) *
          xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n -
        2 * ((n + 1 : ℕ) : ℝ) * HTGeometry.monicOrthoBeta
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) *
          xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n ^ (2 : ℕ)) y := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  have hHn : (HTGeometry.momentHankelMatrix s (n + 2)).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hH
  have hHnext : (HTGeometry.momentHankelMatrix s ((n + 1) + 2)).PosDef := by
    simpa only [s, Nat.add_assoc] using hH
  have hPn : (HTGeometry.monicOrtho s n).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y n := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHn]
  have hPnext : (HTGeometry.monicOrtho s (n + 1)).eval y⁻¹ =
      xiShiftedCanonicalAdmissionApexValue y (n + 1) := by
    rw [xiShiftedCanonicalAdmissionApexValue,
      xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hHnext]
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hfirst := HTGeometry.monicOrthoFirstCoeff_succ_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 3)
  have hrecPoly := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n + 1) (by omega : n + 1 + 1 ≤ n + 3)
  have hrec := congrArg (fun p : Polynomial ℝ => p.eval y⁻¹) hrecPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at hrec
  simp only [s] at hPn hPnext
  rw [show n + 1 - 1 = n by omega, hPn, hPnext] at hrec
  have hAn := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    hy hn hHn
  have hAnext := hasDerivAt_xiShiftedCanonicalAdmissionApexValue_eq_next
    (n := n + 1) hy (by omega) hH
  rw [hPnext] at hAn
  have hrec' :
      (HTGeometry.monicOrtho s (n + 2)).eval y⁻¹ =
        (y⁻¹ - HTGeometry.monicOrthoAlpha s (n + 1)) *
          xiShiftedCanonicalAdmissionApexValue y (n + 1) -
        HTGeometry.monicOrthoBeta s (n + 1) *
          xiShiftedCanonicalAdmissionApexValue y n := by
    rw [show n + 2 = n + 1 + 1 by omega]
    linarith [hrec]
  simp only [s] at hrec'
  rw [hrec'] at hAnext
  have hQuot := hAn.div hAnext hdenom
  refine hQuot.congr_deriv ?_
  simp only [xiShiftedCanonicalAdmissionApexProjectiveTopRatio]
  rw [hfirst]
  field_simp [hdenom, ne_of_gt hy]
  push_cast
  ring

theorem xiShiftedArcsineAdmissionAmplitude_eval_one (n : ℕ) :
    (XiShiftedCanonicalAdmission.Arc.amplitude n).eval 1 =
      XiShiftedCanonicalAdmission.Arc.monicScale n := by
  simp only [XiShiftedCanonicalAdmission.Arc.amplitude,
    XiShiftedArcsineAdmission.amplitude, Polynomial.eval_smul, Polynomial.eval_comp]
  rw [show XiShiftedArcsineAdmission.affine.eval 1 = 1 by
    norm_num [XiShiftedArcsineAdmission.affine]]
  rw [Polynomial.Chebyshev.T_eval_one]
  simp

theorem tendsto_xiShiftedDimensionlessAdmission_eval_one
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ =>
      (XiShiftedCanonicalAdmission.dimensionlessAdmission w n).eval 1) atTop
      (nhds ((XiShiftedCanonicalAdmission.Arc.amplitude n).eval 1)) := by
  rw [show (fun w : ℝ =>
      (XiShiftedCanonicalAdmission.dimensionlessAdmission w n).eval 1) =
      (fun w : ℝ => ∑ k ∈ Finset.range (n + 1),
        (XiShiftedCanonicalAdmission.dimensionlessAdmission w n).coeff k) by
    funext w
    rw [Polynomial.eval_eq_sum_range,
      XiShiftedCanonicalAdmission.dimensionlessAdmission_natDegree]
    simp]
  rw [show (XiShiftedCanonicalAdmission.Arc.amplitude n).eval 1 =
      ∑ k ∈ Finset.range (n + 1),
        (XiShiftedCanonicalAdmission.Arc.amplitude n).coeff k by
    rw [Polynomial.eval_eq_sum_range,
      XiShiftedCanonicalAdmission.arc_amplitude_natDegree_all]
    simp]
  exact tendsto_finsetSum (Finset.range (n + 1)) fun k _ =>
    XiShiftedCanonicalAdmission.tendsto_dimensionlessAdmission_coeff hn k

theorem xiShiftedSourceCoordinateAdmission_eval_inv_square
    {w : ℝ} (hw : w ≠ 0) (n : ℕ) :
    (XiShiftedCanonicalAdmission.sourceCoordinateAdmission w n).eval (w ^ (2 : ℕ))⁻¹ =
      (w ^ (2 * n))⁻¹ *
        (XiShiftedCanonicalAdmission.dimensionlessAdmission w n).eval 1 := by
  simp only [XiShiftedCanonicalAdmission.sourceCoordinateAdmission,
    Polynomial.eval_smul, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, smul_eq_mul]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 hw)]

theorem xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_eq_dimensionlessRatio
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 3)).PosDef) :
    xiShiftedCanonicalAdmissionApexProjectiveTopRatio (w ^ (2 : ℕ)) n / w ^ (2 : ℕ) =
      (XiShiftedCanonicalAdmission.dimensionlessAdmission w n).eval 1 /
        (XiShiftedCanonicalAdmission.dimensionlessAdmission w (n + 1)).eval 1 := by
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hNn := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n ≤ n + 3) hN
  have hNnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 3) hN
  have hAn := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n ≤ n + 3) hA
  have hAnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 3) hA
  have hsourceN := XiShiftedCanonicalAdmission.sourceCoordinateAdmission_eq_actualAdmission
    hw hn (ne_of_gt hNn.det_pos) (ne_of_gt hAn.det_pos)
  have hsourceNext := XiShiftedCanonicalAdmission.sourceCoordinateAdmission_eq_actualAdmission
    hw (by omega : 0 < n + 1) (ne_of_gt hNnext.det_pos) (ne_of_gt hAnext.det_pos)
  have hevalN := congrArg (fun p : Polynomial ℝ => p.eval (w ^ (2 : ℕ))⁻¹) hsourceN
  have hevalNext := congrArg (fun p : Polynomial ℝ => p.eval (w ^ (2 : ℕ))⁻¹) hsourceNext
  rw [xiShiftedSourceCoordinateAdmission_eval_inv_square hw0 n] at hevalN
  rw [xiShiftedSourceCoordinateAdmission_eval_inv_square hw0 (n + 1)] at hevalNext
  rw [xiShiftedCanonicalAdmissionApexProjectiveTopRatio,
    xiShiftedCanonicalAdmissionApexValue, xiShiftedCanonicalAdmissionApexValue,
    ← hevalN, ← hevalNext]
  field_simp [hw0]
  ring

theorem tendsto_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_div_square_four
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ =>
      xiShiftedCanonicalAdmissionApexProjectiveTopRatio (w ^ (2 : ℕ)) n / w ^ (2 : ℕ))
      atTop (nhds 4) := by
  have hQn := tendsto_xiShiftedDimensionlessAdmission_eval_one (Nat.ne_of_gt hn)
  have hQnext := tendsto_xiShiftedDimensionlessAdmission_eval_one
    (by omega : n + 1 ≠ 0)
  rw [xiShiftedArcsineAdmissionAmplitude_eval_one] at hQn hQnext
  have hscaleNextNe : XiShiftedCanonicalAdmission.Arc.monicScale (n + 1) ≠ 0 := by
    unfold XiShiftedCanonicalAdmission.Arc.monicScale
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  have hscaleNNe : XiShiftedCanonicalAdmission.Arc.monicScale n ≠ 0 := by
    unfold XiShiftedCanonicalAdmission.Arc.monicScale
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  have hquot := hQn.div hQnext hscaleNextNe
  have hscale := XiShiftedCanonicalAdmission.arc_monicScale_succ hn
  rw [show XiShiftedCanonicalAdmission.Arc.monicScale n /
      XiShiftedCanonicalAdmission.Arc.monicScale (n + 1) = 4 by
    rw [hscale]
    field_simp [hscaleNNe]] at hquot
  apply hquot.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  exact (xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_eq_dimensionlessRatio hw hn hN' hA).symm

theorem tendsto_square_mul_xiShiftedActualMonicOrthoAlpha_half (n : ℕ) :
    Tendsto (fun w : ℝ => w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n)
      atTop (nhds (1 / 2 : ℝ)) := by
  have h := XiShiftedCanonicalAdmission.tendsto_dimensionless_monicOrthoAlpha n
  apply h.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  exact XiShiftedCanonicalAdmission.normalizedAlpha_eq_square_mul_actualAlpha
    hw n hN' hA

theorem tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1))
      atTop (nhds (1 / 16 : ℝ)) := by
  have h := XiShiftedCanonicalAdmission.tendsto_dimensionless_monicOrthoBeta
    (n := n + 1) (by omega)
  rw [XiShiftedCanonicalAdmission.monicOrthoBeta_normalizedCentralBinom_of_two_le
    (by omega : 2 ≤ n + 1)] at h
  apply h.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 4),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 4),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  exact XiShiftedCanonicalAdmission.normalizedBeta_eq_fourth_mul_actualBeta
    hw (n + 1) hN' hA

theorem tendsto_deriv_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_four
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => deriv
      (fun y => xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n) (w ^ (2 : ℕ)))
      atTop (nhds 4) := by
  let r : ℝ → ℝ := fun w =>
    xiShiftedCanonicalAdmissionApexProjectiveTopRatio (w ^ (2 : ℕ)) n / w ^ (2 : ℕ)
  let a : ℝ → ℝ := fun w => w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
    (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
  let b : ℝ → ℝ := fun w => w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
    (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1)
  have hr : Tendsto r atTop (nhds 4) :=
    tendsto_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_div_square_four hn
  have ha : Tendsto a atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_square_mul_xiShiftedActualMonicOrthoAlpha_half n
  have hb : Tendsto b atTop (nhds (1 / 16 : ℝ)) :=
    tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth hn
  have hE : Tendsto (fun w : ℝ =>
      -2 * (n : ℝ) +
        ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1) * a w) * r w -
        2 * ((n + 1 : ℕ) : ℝ) * b w * r w ^ (2 : ℕ))
      atTop (nhds 4) := by
    have hc0 : Tendsto (fun _ : ℝ => -2 * (n : ℝ)) atTop
        (nhds (-2 * (n : ℝ))) := tendsto_const_nhds
    have hc1 : Tendsto (fun _ : ℝ => 2 * (n : ℝ) + 1) atTop
        (nhds (2 * (n : ℝ) + 1)) := tendsto_const_nhds
    have hc2a : Tendsto (fun w : ℝ => (2 * (n : ℝ) - 1) * a w) atTop
        (nhds ((2 * (n : ℝ) - 1) * (1 / 2 : ℝ))) :=
      ha.const_mul (2 * (n : ℝ) - 1)
    have hc2 : Tendsto (fun w : ℝ =>
        (2 * ((n + 1 : ℕ) : ℝ)) * b w) atTop
        (nhds ((2 * ((n + 1 : ℕ) : ℝ)) * (1 / 16 : ℝ))) :=
      hb.const_mul (2 * ((n + 1 : ℕ) : ℝ))
    have hraw := (hc0.add ((hc1.sub hc2a).mul hr)).sub (hc2.mul (hr.pow 2))
    convert hraw using 1
    · norm_num
      ring
  apply hE.congr'
  have hQnext := tendsto_xiShiftedDimensionlessAdmission_eval_one
    (by omega : n + 1 ≠ 0)
  rw [xiShiftedArcsineAdmissionAmplitude_eval_one] at hQnext
  have hscaleNextNe : XiShiftedCanonicalAdmission.Arc.monicScale (n + 1) ≠ 0 := by
    unfold XiShiftedCanonicalAdmission.Arc.monicScale
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 4),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 4),
    eventually_gt_atTop (1 : ℝ), hQnext.eventually_ne hscaleNextNe]
      with w hN hA hw hQnextNe
  have hw0 : w ≠ 0 := ne_of_gt (lt_trans zero_lt_one hw)
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 4)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 4)).PosDef := hA
  have hNnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 4) hN'
  have hAnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 4) hA'
  have hsourceNext :=
    XiShiftedCanonicalAdmission.sourceCoordinateAdmission_eq_actualAdmission
      hw (by omega : 0 < n + 1) (ne_of_gt hNnext.det_pos) (ne_of_gt hAnext.det_pos)
  have hdenom : xiShiftedCanonicalAdmissionApexValue (w ^ (2 : ℕ)) (n + 1) ≠ 0 := by
    rw [xiShiftedCanonicalAdmissionApexValue, ← hsourceNext,
      xiShiftedSourceCoordinateAdmission_eval_inv_square hw0]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hw0)) hQnextNe
  have hA3 := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 3 ≤ n + 4) hA'
  have hd := hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_eq_riccati (sq_pos_of_pos (lt_trans zero_lt_one hw))
    hn hA3 hdenom
  rw [hd.deriv]
  simp only [r, a, b]
  field_simp [hw0]

theorem deriv_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_eventually_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ w : ℝ in atTop, 0 < deriv
      (fun y => xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n) (w ^ (2 : ℕ)) := by
  exact (tendsto_deriv_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_four hn).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 4))

def xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant (y : ℝ) (n : ℕ) : ℝ :=
  (((2 * (n : ℝ) + 1) / y - (2 * (n : ℝ) - 1) *
      HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment y k).re) n) ^ (2 : ℕ) -
    16 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) *
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1))

theorem tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => w ^ (4 : ℕ) *
      xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant (w ^ (2 : ℕ)) n) atTop
      (nhds (2 * (n : ℝ) + 9 / 4)) := by
  let a : ℝ → ℝ := fun w => w ^ (2 : ℕ) * HTGeometry.monicOrthoAlpha
    (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
  let b : ℝ → ℝ := fun w => w ^ (4 : ℕ) * HTGeometry.monicOrthoBeta
    (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 1)
  have ha : Tendsto a atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_square_mul_xiShiftedActualMonicOrthoAlpha_half n
  have hb : Tendsto b atTop (nhds (1 / 16 : ℝ)) :=
    tendsto_fourth_mul_xiShiftedActualMonicOrthoBeta_succ_sixteenth hn
  have hc : Tendsto (fun _ : ℝ => 2 * (n : ℝ) + 1) atTop
      (nhds (2 * (n : ℝ) + 1)) := tendsto_const_nhds
  have hd : Tendsto (fun w : ℝ => (2 * (n : ℝ) - 1) * a w) atTop
      (nhds ((2 * (n : ℝ) - 1) * (1 / 2 : ℝ))) :=
    ha.const_mul (2 * (n : ℝ) - 1)
  have he : Tendsto (fun w : ℝ =>
      16 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * b w) atTop
      (nhds (16 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * (1 / 16 : ℝ))) :=
    hb.const_mul (16 * (n : ℝ) * ((n + 1 : ℕ) : ℝ))
  have hraw := ((hc.sub hd).pow 2).sub he
  have hlimit : Tendsto (fun w : ℝ =>
      ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1) * a w) ^ (2 : ℕ) -
        16 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) * b w) atTop
      (nhds (2 * (n : ℝ) + 9 / 4)) := by
    convert hraw using 1
    · norm_num
      ring
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
  have hw0 : w ≠ 0 := ne_of_gt hw
  simp only [xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant, a, b]
  field_simp [hw0]

theorem xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant_eventually_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ w : ℝ in atTop,
      0 < xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant (w ^ (2 : ℕ)) n := by
  have hlimit : 0 < 2 * (n : ℝ) + 9 / 4 := by positivity
  have hscaled :=
    (tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveRiccatiDiscriminant hn).eventually
      (Ioi_mem_nhds hlimit)
  filter_upwards [hscaled, eventually_gt_atTop (0 : ℝ)] with w hscaledPos hw
  have hw4 : 0 < w ^ (4 : ℕ) := pow_pos hw 4
  nlinarith

end
end RHTower
