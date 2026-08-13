import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexProjectivePhaseReversal

/-!
# Shifted-Xi compact projective angular phase reversal

Defines the pole-free angular velocity of the adjacent characteristic-apex line.  Finite
positivity makes its projective norm denominator strictly positive.  Both coordinate axes have
negative angular velocity, while shifted-Xi recession forces eventual positive velocity and
the exact scaled limit 1/4 at infinity.
-/

open Complex Matrix Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

def xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity (y : ℝ) (n : ℕ) : ℝ :=
  (xiShiftedCanonicalAdmissionApexValue y (n + 1) * deriv
      (fun v => xiShiftedCanonicalAdmissionApexValue v n) y -
    xiShiftedCanonicalAdmissionApexValue y n * deriv
      (fun v => xiShiftedCanonicalAdmissionApexValue v (n + 1)) y) /
    (xiShiftedCanonicalAdmissionApexValue y n ^ 2 +
      xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ 2)

theorem xiShiftedCanonicalAdmissionApexProjectiveNormSq_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    0 < xiShiftedCanonicalAdmissionApexValue y n ^ 2 +
      xiShiftedCanonicalAdmissionApexValue y (n + 1) ^ 2 := by
  by_cases hAn : xiShiftedCanonicalAdmissionApexValue y n = 0
  · have hNextNe := xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
      hy hn hH hAn
    rw [hAn]
    simpa using sq_pos_of_ne_zero hNextNe
  · have hAnSq : 0 < xiShiftedCanonicalAdmissionApexValue y n ^ 2 :=
      sq_pos_of_ne_zero hAn
    nlinarith [sq_nonneg (xiShiftedCanonicalAdmissionApexValue y (n + 1))]

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_eq_deriv_ratio
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hdenom : xiShiftedCanonicalAdmissionApexValue y (n + 1) ≠ 0) :
    xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity y n =
      deriv (fun v => xiShiftedCanonicalAdmissionApexProjectiveTopRatio v n) y /
        (1 + xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n ^ 2) := by
  rw [(hasDerivAt_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_eq_riccati
    hy hn hH hdenom).deriv]
  unfold xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity
  rw [xiShiftedCanonicalAdmissionApexProjectiveWronskian_eq_riccatiQuadratic
    hy hn hH]
  simp only [xiShiftedCanonicalAdmissionApexProjectiveTopRatio]
  field_simp [hdenom]
  ring

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_numerator_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity y n = -2 * (n : ℝ) := by
  have hNextNe := xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
    hy hn hH hcontact
  unfold xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity
  rw [xiShiftedCanonicalAdmissionApexProjectiveWronskian_eq_riccatiQuadratic
    hy hn hH, hcontact]
  field_simp [hNextNe]
  ring

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_numerator_contact_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y n = 0) :
    xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity y n < 0 := by
  rw [xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_numerator_contact hy hn hH hcontact]
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  linarith

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_denominator_contact
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y (n + 1) = 0) :
    xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity y n = -2 * ((n + 1 : ℕ) : ℝ) *
      HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) := by
  have hAnNe : xiShiftedCanonicalAdmissionApexValue y n ≠ 0 := by
    intro hAn
    exact (xiShiftedCanonicalAdmissionApexValue_succ_ne_zero_of_contact
      hy hn hH hAn) hcontact
  unfold xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity
  rw [xiShiftedCanonicalAdmissionApexProjectiveWronskian_eq_riccatiQuadratic
    hy hn hH, hcontact]
  field_simp [hAnNe]
  ring

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_denominator_contact_neg
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef)
    (hcontact : xiShiftedCanonicalAdmissionApexValue y (n + 1) = 0) :
    xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity y n < 0 := by
  rw [xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_denominator_contact hy hn hH hcontact]
  have hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  have hn1R : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcoeff : -2 * ((n + 1 : ℕ) : ℝ) < 0 := by linarith
  exact mul_neg_of_neg_of_pos hcoeff hbeta

theorem tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_quarter
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun w : ℝ => w ^ 4 * xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity (w ^ 2) n)
      atTop (nhds (1 / 4 : ℝ)) := by
  let r : ℝ → ℝ := fun w =>
    xiShiftedCanonicalAdmissionApexProjectiveTopRatio (w ^ 2) n / w ^ 2
  let d : ℝ → ℝ := fun w => deriv
    (fun y => xiShiftedCanonicalAdmissionApexProjectiveTopRatio y n) (w ^ 2)
  have hr : Tendsto r atTop (nhds 4) :=
    tendsto_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_div_square_four hn
  have hd : Tendsto d atTop (nhds 4) :=
    tendsto_deriv_xiShiftedCanonicalAdmissionApexProjectiveTopRatio_square_four hn
  have hinv4 : Tendsto (fun w : ℝ => w⁻¹ ^ 4) atTop (nhds 0) :=
    by simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 4)
  have hden : Tendsto (fun w : ℝ => w⁻¹ ^ 4 + r w ^ 2) atTop (nhds 16) := by
    have hraw := hinv4.add (hr.pow 2)
    convert hraw using 1
    · norm_num
  have hlim : Tendsto (fun w : ℝ => d w / (w⁻¹ ^ 4 + r w ^ 2)) atTop
      (nhds (1 / 4 : ℝ)) := by
    have hraw := hd.div hden (by norm_num : (16 : ℝ) ≠ 0)
    convert hraw using 1
    · ext w
      rfl
    · norm_num
  apply hlim.congr'
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
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 4)).PosDef := hA
  have hNnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 4) hN'
  have hAnext := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 1 ≤ n + 4) hA'
  have hsourceNext :=
    XiShiftedCanonicalAdmission.sourceCoordinateAdmission_eq_actualAdmission
      hw (by omega : 0 < n + 1) (ne_of_gt hNnext.det_pos) (ne_of_gt hAnext.det_pos)
  have hdenom : xiShiftedCanonicalAdmissionApexValue (w ^ 2) (n + 1) ≠ 0 := by
    rw [xiShiftedCanonicalAdmissionApexValue, ← hsourceNext,
      xiShiftedSourceCoordinateAdmission_eval_inv_square hw0]
    exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hw0)) hQnextNe
  have hA3 := XiShiftedCanonicalAdmission.momentHankel_posDef_of_le
    (by omega : n + 3 ≤ n + 4) hA'
  rw [xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_eq_deriv_ratio
    (sq_pos_of_pos (lt_trans zero_lt_one hw)) hn hA3 hdenom]
  simp only [r, d]
  field_simp [hw0]

theorem xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_square_eventually_pos
    {n : ℕ} (hn : 0 < n) :
    ∀ᶠ w : ℝ in atTop, 0 < xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity (w ^ 2) n := by
  have hscaled := (tendsto_fourth_mul_xiShiftedCanonicalAdmissionApexProjectiveAngularVelocity_quarter hn).eventually
    (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hscaled, eventually_gt_atTop (0 : ℝ)] with w hscaledPos hw
  have hw4 : 0 < w ^ 4 := pow_pos hw 4
  nlinarith

end
end RHTower

