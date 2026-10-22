import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureHeightLocalFrame

/-!
# Adjacent Hedenmalm features detect every nonreal reflected pair by Krein index

Two adjacent real-centered Hedenmalm critical features give a fixed two-channel reporter.  Their
evaluation determinant on a point and its conjugate factors explicitly.  Nearest-integer routing
makes its remaining real factor strictly positive throughout the open critical strip, so the
determinant is nonzero exactly away from the critical line.

The associated reflected Weil block is therefore strictly indefinite at every nonreal point: two
explicit vectors have quadratic values `2 Δ²` and `-2 Δ²`.  At the critical line its determinant
is zero.  This is a magnitude-free, collision-stable index separator; its negative eigenvalue can
still tend to zero, so no quantitative source budget is claimed.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Evaluation determinant of adjacent real-centered critical features on `z` and `conj z`. -/
def adjacentCriticalFeatureEvaluationDet
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) : ℂ :=
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  criticalEvaluation z hz
      (criticalFeature (t : ℂ) (by norm_num)) *
    criticalEvaluation ((starRingEnd ℂ) z) hzc
      (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num)) -
  criticalEvaluation ((starRingEnd ℂ) z) hzc
      (criticalFeature (t : ℂ) (by norm_num)) *
    criticalEvaluation z hz
      (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))

/-- Exact rational factorization of the adjacent-feature evaluation determinant. -/
theorem adjacentCriticalFeatureEvaluationDet_eq
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    adjacentCriticalFeatureEvaluationDet t z hz =
      (-16 : ℂ) * I * z.im *
        (1 - z.im ^ (2 : ℕ) - (z.re - t) * (z.re - (t + 1))) /
        ((1 + (z - (t : ℂ)) ^ (2 : ℕ)) *
          (1 + ((starRingEnd ℂ) z - (t : ℂ)) ^ (2 : ℕ)) *
          (1 + (z - ((t + 1 : ℝ) : ℂ)) ^ (2 : ℕ)) *
          (1 + ((starRingEnd ℂ) z - ((t + 1 : ℝ) : ℂ)) ^ (2 : ℕ))) := by
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  have htz := criticalFeatureKernelDenominator_ne_zero
    (w := (t : ℂ)) (z := z) (by norm_num) hz
  have htcz := criticalFeatureKernelDenominator_ne_zero
    (w := (t : ℂ)) (z := (starRingEnd ℂ) z) (by norm_num) hzc
  have hsz := criticalFeatureKernelDenominator_ne_zero
    (w := ((t + 1 : ℝ) : ℂ)) (z := z) (by norm_num) hz
  have hscz := criticalFeatureKernelDenominator_ne_zero
    (w := ((t + 1 : ℝ) : ℂ)) (z := (starRingEnd ℂ) z) (by norm_num) hzc
  rw [adjacentCriticalFeatureEvaluationDet]
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz,
    criticalEvaluation_criticalFeature_eq (by norm_num) hzc,
    criticalEvaluation_criticalFeature_eq (by norm_num) hzc,
    criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  simp only [Complex.conj_ofReal]
  have hnum :
      (1 + ((starRingEnd ℂ) z - (t : ℂ)) ^ (2 : ℕ)) *
          (1 + (z - ((t + 1 : ℝ) : ℂ)) ^ (2 : ℕ)) -
        (1 + (z - (t : ℂ)) ^ (2 : ℕ)) *
          (1 + ((starRingEnd ℂ) z - ((t + 1 : ℝ) : ℂ)) ^ (2 : ℕ)) =
        (-4 : ℂ) * I * z.im *
          (1 - z.im ^ (2 : ℕ) - (z.re - t) * (z.re - (t + 1))) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, pow_two] <;>
      ring
  simp only [Complex.conj_ofReal] at htz htcz hsz hscz
  field_simp [htz, htcz, hsz, hscz]
  rw [hnum]
  ring

/-- Nearest-center strip geometry makes the determinant's non-height factor positive. -/
theorem adjacentCriticalFeatureNumerator_pos_of_abs_sub_le_half
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    0 < 1 - z.im ^ (2 : ℕ) - (z.re - t) * (z.re - (t + 1)) := by
  have him2 : z.im ^ (2 : ℕ) < 1 / 4 := by
    have hsq := (sq_lt_sq₀ (abs_nonneg z.im)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hz
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have huLower : -(1 / 2 : ℝ) ≤ z.re - t := (abs_le.mp ht).1
  have huUpper : z.re - t ≤ (1 / 2 : ℝ) := (abs_le.mp ht).2
  nlinarith [mul_nonneg (sub_nonneg.mpr huUpper)
    (show 0 ≤ 3 / 2 + (z.re - t) by linarith)]

/-- Adjacent-feature determinant is nonzero at every nonreal strip point near the first center. -/
theorem adjacentCriticalFeatureEvaluationDet_ne_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (hy : z.im ≠ 0) (ht : |z.re - t| ≤ 1 / 2) :
    adjacentCriticalFeatureEvaluationDet t z hz ≠ 0 := by
  rw [adjacentCriticalFeatureEvaluationDet_eq]
  have hfactor := adjacentCriticalFeatureNumerator_pos_of_abs_sub_le_half t hz ht
  have hden1 := criticalFeatureKernelDenominator_ne_zero
    (w := (t : ℂ)) (z := z) (by norm_num) hz
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  have hden2 := criticalFeatureKernelDenominator_ne_zero
    (w := (t : ℂ)) (z := (starRingEnd ℂ) z) (by norm_num) hzc
  have hden3 := criticalFeatureKernelDenominator_ne_zero
    (w := ((t + 1 : ℝ) : ℂ)) (z := z) (by norm_num) hz
  have hden4 := criticalFeatureKernelDenominator_ne_zero
    (w := ((t + 1 : ℝ) : ℂ)) (z := (starRingEnd ℂ) z) (by norm_num) hzc
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
        (ofReal_ne_zero.mpr hy))
      (by exact_mod_cast hfactor.ne')
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (by simpa only [Complex.conj_ofReal] using hden1)
      (by simpa only [Complex.conj_ofReal] using hden2))
      (by simpa only [Complex.conj_ofReal] using hden3))
      (by simpa only [Complex.conj_ofReal] using hden4)

/-- Nearest-integer adjacent features detect every nonreal point of the open strip. -/
theorem adjacentCriticalFeatureEvaluationDet_round_ne_zero
    {z : ℂ} (hz : |z.im| < 1 / 2) (hy : z.im ≠ 0) :
    adjacentCriticalFeatureEvaluationDet ((round z.re : ℤ) : ℝ) z hz ≠ 0 :=
  adjacentCriticalFeatureEvaluationDet_ne_zero _ hz hy (abs_sub_round _)

/-- Determinant of the real symmetric reflected pair block `2(xxᵀ-yyᵀ)`. -/
def reflectedPairBlockDet (a b : ℂ) : ℝ :=
  let x0 := a.re
  let x1 := b.re
  let y0 := a.im
  let y1 := b.im
  (2 * (x0 ^ (2 : ℕ) - y0 ^ (2 : ℕ))) * (2 * (x1 ^ (2 : ℕ) - y1 ^ (2 : ℕ))) -
    (2 * (x0 * x1 - y0 * y1)) ^ (2 : ℕ)

/-- Oriented real area of two complex coordinates. -/
def complexPairArea (a b : ℂ) : ℝ :=
  a.re * b.im - a.im * b.re

/-- Reflected pair-block determinant is minus four times squared coordinate area. -/
theorem reflectedPairBlockDet_eq (a b : ℂ) :
    reflectedPairBlockDet a b = -4 * complexPairArea a b ^ (2 : ℕ) := by
  rw [reflectedPairBlockDet, complexPairArea]
  ring

/-- Evaluation by a real-centered critical feature intertwines complex conjugation. -/
theorem criticalEvaluation_realCriticalFeature_conj_eq
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
    criticalEvaluation ((starRingEnd ℂ) z) hzc
        (criticalFeature (t : ℂ) (by norm_num)) =
      (starRingEnd ℂ)
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num))) := by
  dsimp only
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) (by simpa using hz),
    criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  simp only [Complex.conj_ofReal, map_div₀, map_ofNat, map_add, map_one,
    map_pow, map_sub]

/-- Evaluation determinant is `-2i` times the real coordinate area. -/
theorem adjacentCriticalFeatureEvaluationDet_eq_area
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    adjacentCriticalFeatureEvaluationDet t z hz =
      (-2 : ℂ) * I *
        complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) := by
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  rw [adjacentCriticalFeatureEvaluationDet]
  rw [criticalEvaluation_realCriticalFeature_conj_eq (t + 1) hz,
    criticalEvaluation_realCriticalFeature_conj_eq t hz]
  apply Complex.ext
  · simp [complexPairArea, Complex.mul_re, Complex.mul_im]
  · simp [complexPairArea, Complex.mul_re, Complex.mul_im]
    ring

/-- Adjacent evaluation coordinates have nonzero real area off the critical line. -/
theorem complexPairArea_adjacentCriticalFeature_ne_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (hy : z.im ≠ 0) (ht : |z.re - t| ≤ 1 / 2) :
    complexPairArea
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) ≠ 0 := by
  intro harea
  have hdet := adjacentCriticalFeatureEvaluationDet_ne_zero t hz hy ht
  apply hdet
  rw [adjacentCriticalFeatureEvaluationDet_eq_area, harea]
  simp

/-- The actual reflected pair block has negative determinant at every nonreal strip point. -/
theorem reflectedPairBlockDet_adjacentCriticalFeature_neg
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (hy : z.im ≠ 0) (ht : |z.re - t| ≤ 1 / 2) :
    reflectedPairBlockDet
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) < 0 := by
  rw [reflectedPairBlockDet_eq]
  have harea := complexPairArea_adjacentCriticalFeature_ne_zero t hz hy ht
  nlinarith [sq_pos_of_ne_zero harea]

/-- Quadratic form of the real symmetric reflected pair block. -/
def reflectedPairBlockQuadratic (a b : ℂ) (u v : ℝ) : ℝ :=
  2 * ((a.re * u + b.re * v) ^ (2 : ℕ) - (a.im * u + b.im * v) ^ (2 : ℕ))

/-- Vector perpendicular to the imaginary part has positive reflected-pair value. -/
theorem reflectedPairBlockQuadratic_positiveWitness (a b : ℂ) :
    reflectedPairBlockQuadratic a b b.im (-a.im) =
      2 * complexPairArea a b ^ (2 : ℕ) := by
  rw [reflectedPairBlockQuadratic, complexPairArea]
  ring

/-- Vector perpendicular to the real part has negative reflected-pair value. -/
theorem reflectedPairBlockQuadratic_negativeWitness (a b : ℂ) :
    reflectedPairBlockQuadratic a b b.re (-a.re) =
      -2 * complexPairArea a b ^ (2 : ℕ) := by
  rw [reflectedPairBlockQuadratic, complexPairArea]
  ring

/-- Adjacent features make every nonreal reflected pair block strictly indefinite. -/
theorem adjacentCriticalFeature_reflectedPair_indefinite
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (hy : z.im ≠ 0) (ht : |z.re - t| ≤ 1 / 2) :
    let a := criticalEvaluation z hz
      (criticalFeature (t : ℂ) (by norm_num))
    let b := criticalEvaluation z hz
      (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))
    0 < reflectedPairBlockQuadratic a b b.im (-a.im) ∧
      reflectedPairBlockQuadratic a b b.re (-a.re) < 0 := by
  dsimp only
  rw [reflectedPairBlockQuadratic_positiveWitness,
    reflectedPairBlockQuadratic_negativeWitness]
  have harea := complexPairArea_adjacentCriticalFeature_ne_zero t hz hy ht
  have hsquare := sq_pos_of_ne_zero harea
  constructor <;> nlinarith

/-- Real-line points have real evaluation in every real-centered feature. -/
theorem criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) (hzim : z.im = 0) :
    (criticalEvaluation z hz
      (criticalFeature (t : ℂ) (by norm_num))).im = 0 := by
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  have hdenIm : (1 + (z - (t : ℂ)) ^ (2 : ℕ)).im = 0 := by
    simp [pow_two, Complex.mul_im, hzim]
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_im]
  simp [hdenIm]

/-- At the critical line the adjacent-feature reflected block has zero determinant. -/
theorem reflectedPairBlockDet_adjacentCriticalFeature_eq_zero_of_im_eq_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) (hzim : z.im = 0) :
    reflectedPairBlockDet
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) = 0 := by
  rw [reflectedPairBlockDet_eq, complexPairArea,
    criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero t hz hzim,
    criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero (t + 1) hz hzim]
  ring

/-- Every actual strict-right Xi copy has negative adjacent-feature pair-block determinant. -/
theorem reflectedPairBlockDet_adjacentCriticalFeature_xiRight_round_neg
    (q : XiRightZeroCopy) :
    reflectedPairBlockDet
        (criticalEvaluation (xiSpectralPoint q.1)
          (abs_xiSpectralPoint_im_lt_half q.1)
          (criticalFeature
            (((round (xiSpectralPoint q.1).re : ℤ) : ℝ) : ℂ) (by norm_num)))
        (criticalEvaluation (xiSpectralPoint q.1)
          (abs_xiSpectralPoint_im_lt_half q.1)
          (criticalFeature
            (((round (xiSpectralPoint q.1).re : ℤ) : ℝ) + 1 : ℂ) (by norm_num))) < 0 := by
  have hy : (xiSpectralPoint q.1).im ≠ 0 := by
    have hrel : -(xiSpectralPoint q.1).im = (xiRightCenteredZero q).re := by
      rw [xiRightCenteredZero]
      simp [Complex.mul_re]
    intro hy0
    have hpos := xiRightCenteredZero_re_pos q
    rw [← hrel, hy0] at hpos
    linarith
  have h := reflectedPairBlockDet_adjacentCriticalFeature_neg
    (((round (xiSpectralPoint q.1).re : ℤ) : ℝ))
    (abs_xiSpectralPoint_im_lt_half q.1) hy (abs_sub_round _)
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using h

end

end RHTower
