import GaloisForLFunctions.RHTower.HedenmalmAdjacentFeatureKreinIndexSeparator

/-!
# Quantitative transverse determinant of oriented adjacent critical features

The adjacent-feature Krein index survives submicroscopic coalescence qualitatively.  Orienting the
second reporter toward the nearest-center cell strengthens this to a uniform quantitative theorem:
after division by the squared transverse displacement, one of two predeclared adjacent blocks has
determinant at most `-4 * (96 / 145)^2` throughout the critical strip.

This closes the local quantitative separator.  A source-native exterior-square trace budget is a
separate global problem; no zero-density conclusion is asserted here.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

def criticalFeatureDenominatorNormSq (t : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq (1 + (z - (t : ℂ)) ^ 2)

theorem criticalFeatureDenominatorNormSq_pos
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    0 < criticalFeatureDenominatorNormSq t z := by
  rw [criticalFeatureDenominatorNormSq]
  exact Complex.normSq_pos.mpr
    (by simpa only [Complex.conj_ofReal] using
      (criticalFeatureKernelDenominator_ne_zero
        (w := (t : ℂ)) (z := z) (by norm_num) hz))

theorem criticalFeatureDenominatorNormSq_eq (t : ℝ) (z : ℂ) :
    criticalFeatureDenominatorNormSq t z =
      (1 + (z.re - t) ^ 2 - z.im ^ 2) ^ 2 +
        (2 * (z.re - t) * z.im) ^ 2 := by
  rw [criticalFeatureDenominatorNormSq, Complex.normSq_apply]
  simp [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem criticalFeatureDenominatorNormSq_le_five
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 2)
    (ht : |z.re - t| ≤ 1) :
    criticalFeatureDenominatorNormSq t z ≤ 5 := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hu2 : u ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1)).2
      (by simpa [u] using ht)
    simpa only [sq_abs, one_pow] using h
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [y] using hy)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hA0 : 0 ≤ 1 + u ^ 2 - y ^ 2 := by nlinarith [sq_nonneg u]
  have hA : 1 + u ^ 2 - y ^ 2 ≤ 2 := by nlinarith
  have hA4 : (1 + u ^ 2 - y ^ 2) ^ 2 ≤ 4 := by
    have := (sq_le_sq₀ hA0 (by norm_num : (0 : ℝ) ≤ 2)).2 hA
    norm_num at this ⊢
    exact this
  have huv : u ^ 2 * y ^ 2 ≤ 1 / 4 := by
    exact (mul_le_mul hu2 hy2 (sq_nonneg y) (by norm_num)).trans_eq (by norm_num)
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hA4 huv ⊢
  ring_nf at ⊢
  linarith

theorem criticalFeatureDenominatorNormSq_le_twentyNineSixteenths
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    criticalFeatureDenominatorNormSq t z ≤ 29 / 16 := by
  let u : ℝ := z.re - t
  let y : ℝ := z.im
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [u] using ht)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2
      (by simpa [y] using hy)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hA0 : 0 ≤ 1 + u ^ 2 - y ^ 2 := by nlinarith [sq_nonneg u]
  have hA : 1 + u ^ 2 - y ^ 2 ≤ 5 / 4 := by nlinarith
  have hAsq : (1 + u ^ 2 - y ^ 2) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 :=
    (sq_le_sq₀ hA0 (by norm_num)).2 hA
  have huv : u ^ 2 * y ^ 2 ≤ 1 / 16 := by
    have := mul_le_mul hu2 hy2 (sq_nonneg y) (by norm_num : 0 ≤ (1 / 4 : ℝ))
    norm_num at this ⊢
    exact this
  rw [criticalFeatureDenominatorNormSq_eq]
  dsimp only [u, y] at hAsq huv ⊢
  ring_nf at ⊢
  norm_num at hAsq ⊢
  linarith

theorem complexPairArea_adjacentCriticalFeature_eq
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    complexPairArea
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) =
      8 * z.im *
        (1 - z.im ^ 2 - (z.re - t) * (z.re - (t + 1))) /
          (criticalFeatureDenominatorNormSq t z *
            criticalFeatureDenominatorNormSq (t + 1) z) := by
  have h0 := criticalFeatureDenominatorNormSq_pos t hz
  have h1 := criticalFeatureDenominatorNormSq_pos (t + 1) hz
  rw [complexPairArea]
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz,
    criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  rw [Complex.div_re, Complex.div_im, Complex.div_re, Complex.div_im]
  norm_num
  simp only [Complex.normSq_apply]
  simp [criticalFeatureDenominatorNormSq, Complex.normSq_apply,
    pow_two, Complex.mul_re, Complex.mul_im]
  field_simp
  ring

theorem complexPairArea_adjacentCriticalFeature_sq_ge_of_nonneg
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) (hu : 0 ≤ z.re - t) :
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
      complexPairArea
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) ^ 2 := by
  let C : ℝ := 1 - z.im ^ 2 - (z.re - t) * (z.re - (t + 1))
  let D0 : ℝ := criticalFeatureDenominatorNormSq t z
  let D1 : ℝ := criticalFeatureDenominatorNormSq (t + 1) z
  let D : ℝ := D0 * D1
  have hy : |z.im| ≤ 1 / 2 := le_of_lt hz
  have huUpper : z.re - t ≤ 1 / 2 := (abs_le.mp ht).2
  have hnext : |z.re - (t + 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hC : 3 / 4 ≤ C := by
    have hy2 : z.im ^ 2 ≤ 1 / 4 := by
      have h := (sq_le_sq₀ (abs_nonneg z.im)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hy
      rw [sq_abs] at h
      norm_num at h ⊢
      exact h
    have hprod : (z.re - t) * (z.re - (t + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hu (by linarith)
    dsimp only [C]
    linarith
  have hD0pos : 0 < D0 := criticalFeatureDenominatorNormSq_pos t hz
  have hD1pos : 0 < D1 := criticalFeatureDenominatorNormSq_pos (t + 1) hz
  have hDpos : 0 < D := mul_pos hD0pos hD1pos
  have hD0 : D0 ≤ 29 / 16 :=
    criticalFeatureDenominatorNormSq_le_twentyNineSixteenths t hy ht
  have hD1 : D1 ≤ 5 :=
    criticalFeatureDenominatorNormSq_le_five (t + 1) hy hnext
  have hD : D ≤ 145 / 16 := by
    dsimp only [D]
    nlinarith [mul_le_mul hD0 hD1 hD1pos.le (by norm_num : 0 ≤ (29 / 16 : ℝ))]
  have hfactorCross : (96 / 145 : ℝ) * D ≤ 8 * C := by
    nlinarith
  have hfactor : (96 / 145 : ℝ) ≤ 8 * C / D := by
    rw [le_div_iff₀ hDpos]
    exact hfactorCross
  have hfactorNonneg : 0 ≤ (96 / 145 : ℝ) := by norm_num
  have hfactorSq : (96 / 145 : ℝ) ^ 2 ≤ (8 * C / D) ^ 2 :=
    pow_le_pow_left₀ hfactorNonneg hfactor 2
  rw [complexPairArea_adjacentCriticalFeature_eq]
  change (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
    (8 * z.im * C / D) ^ 2
  have hmul := mul_le_mul_of_nonneg_right hfactorSq (sq_nonneg z.im)
  calc
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
        (8 * C / D) ^ 2 * z.im ^ 2 := hmul
    _ = (8 * z.im * C / D) ^ 2 := by ring

theorem complexPairArea_previousCriticalFeature_sq_ge_of_nonpos
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) (hu : z.re - t ≤ 0) :
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
      complexPairArea
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t - 1 : ℝ) : ℂ) (by norm_num))) ^ 2 := by
  let C : ℝ :=
    1 - z.im ^ 2 - (z.re - (t - 1)) * (z.re - t)
  let D0 : ℝ := criticalFeatureDenominatorNormSq (t - 1) z
  let D1 : ℝ := criticalFeatureDenominatorNormSq t z
  let D : ℝ := D0 * D1
  have hy : |z.im| ≤ 1 / 2 := le_of_lt hz
  have huLower : -(1 / 2 : ℝ) ≤ z.re - t := (abs_le.mp ht).1
  have hprev : |z.re - (t - 1)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hC : 3 / 4 ≤ C := by
    have hy2 : z.im ^ 2 ≤ 1 / 4 := by
      have h := (sq_le_sq₀ (abs_nonneg z.im)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hy
      rw [sq_abs] at h
      norm_num at h ⊢
      exact h
    have hprod : (z.re - (t - 1)) * (z.re - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hu
    dsimp only [C]
    linarith
  have hD0pos : 0 < D0 := criticalFeatureDenominatorNormSq_pos (t - 1) hz
  have hD1pos : 0 < D1 := criticalFeatureDenominatorNormSq_pos t hz
  have hDpos : 0 < D := mul_pos hD0pos hD1pos
  have hD0 : D0 ≤ 5 :=
    criticalFeatureDenominatorNormSq_le_five (t - 1) hy hprev
  have hD1 : D1 ≤ 29 / 16 :=
    criticalFeatureDenominatorNormSq_le_twentyNineSixteenths t hy ht
  have hD : D ≤ 145 / 16 := by
    dsimp only [D]
    nlinarith [mul_le_mul hD0 hD1 hD1pos.le (by norm_num : 0 ≤ (5 : ℝ))]
  have hfactorCross : (96 / 145 : ℝ) * D ≤ 8 * C := by
    nlinarith
  have hfactor : (96 / 145 : ℝ) ≤ 8 * C / D := by
    rw [le_div_iff₀ hDpos]
    exact hfactorCross
  have hfactorNonneg : 0 ≤ (96 / 145 : ℝ) := by norm_num
  have hfactorSq : (96 / 145 : ℝ) ^ 2 ≤ (8 * C / D) ^ 2 :=
    pow_le_pow_left₀ hfactorNonneg hfactor 2
  have harea := complexPairArea_adjacentCriticalFeature_eq (t - 1) z hz
  have harea' :
      complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (((t - 1 : ℝ)) : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num))) =
        8 * z.im * C / D := by
    simpa only [sub_add_cancel, C, D, D0, D1] using harea
  have hswap :
      complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature (((t - 1 : ℝ)) : ℂ) (by norm_num))) =
        -complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (((t - 1 : ℝ)) : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num))) := by
    rw [complexPairArea, complexPairArea]
    ring
  rw [hswap, harea']
  have hmul := mul_le_mul_of_nonneg_right hfactorSq (sq_nonneg z.im)
  calc
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
        (8 * C / D) ^ 2 * z.im ^ 2 := hmul
    _ = (-(8 * z.im * C / D)) ^ 2 := by ring

/-- One of the two adjacent reporters oriented toward the nearest-center cell has a uniform
inverse-square transverse area quantum. -/
theorem complexPairArea_orientedAdjacentCriticalFeature_sq_ge
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
        complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) ^ 2 ∨
      (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
        complexPairArea
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature ((t - 1 : ℝ) : ℂ) (by norm_num))) ^ 2 := by
  by_cases hu : 0 ≤ z.re - t
  · exact Or.inl
      (complexPairArea_adjacentCriticalFeature_sq_ge_of_nonneg t hz ht hu)
  · exact Or.inr
      (complexPairArea_previousCriticalFeature_sq_ge_of_nonpos t hz ht (le_of_not_ge hu))

/-- The same alternative expressed as a strictly negative, inverse-square-normalized reflected
pair determinant. -/
theorem reflectedPairBlockDet_orientedAdjacentCriticalFeature_div_sq_le
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) (hy : z.im ≠ 0) :
    reflectedPairBlockDet
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) /
        z.im ^ 2 ≤ -4 * (96 / 145 : ℝ) ^ 2 ∨
      reflectedPairBlockDet
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation z hz
            (criticalFeature ((t - 1 : ℝ) : ℂ) (by norm_num))) /
        z.im ^ 2 ≤ -4 * (96 / 145 : ℝ) ^ 2 := by
  have hySq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hy
  rcases complexPairArea_orientedAdjacentCriticalFeature_sq_ge t hz ht with hplus | hminus
  · left
    rw [reflectedPairBlockDet_eq]
    apply (div_le_iff₀ hySq).2
    nlinarith
  · right
    rw [reflectedPairBlockDet_eq]
    apply (div_le_iff₀ hySq).2
    nlinarith

/-- Fixed three-feature exterior-square energy: both adjacent orientations are retained, so no
zero-dependent branch is selected. -/
def orientedAdjacentCriticalFeatureExteriorEnergy
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) : ℝ :=
  complexPairArea
      (criticalEvaluation z hz
        (criticalFeature (t : ℂ) (by norm_num)))
      (criticalEvaluation z hz
        (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) ^ 2 +
    complexPairArea
      (criticalEvaluation z hz
        (criticalFeature (t : ℂ) (by norm_num)))
      (criticalEvaluation z hz
        (criticalFeature ((t - 1 : ℝ) : ℂ) (by norm_num))) ^ 2

/-- One adjacent exterior area is exactly one quarter of the squared norm of the explicit
two-evaluation determinant. -/
theorem four_mul_complexPairArea_sq_eq_normSq_adjacentCriticalFeatureEvaluationDet
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    4 * complexPairArea
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num)))
        (criticalEvaluation z hz
          (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) ^ 2 =
      Complex.normSq (adjacentCriticalFeatureEvaluationDet t z hz) := by
  rw [adjacentCriticalFeatureEvaluationDet_eq_area, Complex.normSq_mul,
    Complex.normSq_mul]
  norm_num [Complex.normSq_apply, complexPairArea]
  ring

/-- The fixed three-feature energy is the sum of two literal source-evaluation determinant
energies.  This is the four-leg quantity whose Euler--Gamma trace remains to be bounded. -/
theorem four_mul_orientedAdjacentCriticalFeatureExteriorEnergy_eq
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    4 * orientedAdjacentCriticalFeatureExteriorEnergy t z hz =
      Complex.normSq (adjacentCriticalFeatureEvaluationDet t z hz) +
        Complex.normSq (adjacentCriticalFeatureEvaluationDet (t - 1) z hz) := by
  rw [orientedAdjacentCriticalFeatureExteriorEnergy,
    ← four_mul_complexPairArea_sq_eq_normSq_adjacentCriticalFeatureEvaluationDet t z hz,
    ← four_mul_complexPairArea_sq_eq_normSq_adjacentCriticalFeatureEvaluationDet
      (t - 1) z hz]
  rw [complexPairArea, complexPairArea, complexPairArea]
  ring_nf

theorem orientedAdjacentCriticalFeatureExteriorEnergy_nonneg
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    0 ≤ orientedAdjacentCriticalFeatureExteriorEnergy t z hz := by
  rw [orientedAdjacentCriticalFeatureExteriorEnergy]
  positivity

/-- The fixed three-feature exterior square has a uniform quadratic transverse floor. -/
theorem orientedAdjacentCriticalFeatureExteriorEnergy_ge
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (96 / 145 : ℝ) ^ 2 * z.im ^ 2 ≤
      orientedAdjacentCriticalFeatureExteriorEnergy t z hz := by
  rcases complexPairArea_orientedAdjacentCriticalFeature_sq_ge t hz ht with hplus | hminus
  · rw [orientedAdjacentCriticalFeatureExteriorEnergy]
    exact hplus.trans (le_add_of_nonneg_right (sq_nonneg _))
  · rw [orientedAdjacentCriticalFeatureExteriorEnergy]
    exact hminus.trans (le_add_of_nonneg_left (sq_nonneg _))

/-- Critical-line multiplicity contributes exactly zero to the exterior-square energy. -/
theorem orientedAdjacentCriticalFeatureExteriorEnergy_eq_zero_of_im_eq_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) (hy : z.im = 0) :
    orientedAdjacentCriticalFeatureExteriorEnergy t z hz = 0 := by
  rw [orientedAdjacentCriticalFeatureExteriorEnergy, complexPairArea, complexPairArea,
    criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero t hz hy,
    criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero (t + 1) hz hy,
    criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero (t - 1) hz hy]
  ring

/-- Singular transverse Green normalization of the exterior-square energy. -/
def orientedAdjacentCriticalFeatureTransverseEnergy
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) : ℝ :=
  z.im⁻¹ ^ 2 * orientedAdjacentCriticalFeatureExteriorEnergy t z hz

/-- Off the critical line, the fixed three-feature transverse energy has the uniform quantum. -/
theorem orientedAdjacentCriticalFeatureTransverseEnergy_ge
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) (hy : z.im ≠ 0) :
    (96 / 145 : ℝ) ^ 2 ≤
      orientedAdjacentCriticalFeatureTransverseEnergy t z hz := by
  have h := orientedAdjacentCriticalFeatureExteriorEnergy_ge t hz ht
  rw [orientedAdjacentCriticalFeatureTransverseEnergy]
  calc
    (96 / 145 : ℝ) ^ 2 = z.im⁻¹ ^ 2 *
        ((96 / 145 : ℝ) ^ 2 * z.im ^ 2) := by field_simp
    _ ≤ z.im⁻¹ ^ 2 * orientedAdjacentCriticalFeatureExteriorEnergy t z hz :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- On the critical line the convention supplied by inverse in Lean makes transverse energy zero,
matching the unnormalized exterior-square cancellation. -/
theorem orientedAdjacentCriticalFeatureTransverseEnergy_eq_zero_of_im_eq_zero
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) (hy : z.im = 0) :
    orientedAdjacentCriticalFeatureTransverseEnergy t z hz = 0 := by
  rw [orientedAdjacentCriticalFeatureTransverseEnergy, hy]
  norm_num

/-- Every strict-right Xi multiplicity copy has one nearest-integer oriented adjacent block with
the uniform transverse determinant quantum. -/
theorem reflectedPairBlockDet_orientedAdjacentCriticalFeature_xiRight_round_div_sq_le
    (q : XiRightZeroCopy) :
    let t : ℝ := ((round (xiSpectralPoint q.1).re : ℤ) : ℝ)
    reflectedPairBlockDet
          (criticalEvaluation (xiSpectralPoint q.1)
            (abs_xiSpectralPoint_im_lt_half q.1)
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation (xiSpectralPoint q.1)
            (abs_xiSpectralPoint_im_lt_half q.1)
            (criticalFeature ((t + 1 : ℝ) : ℂ) (by norm_num))) /
        (xiSpectralPoint q.1).im ^ 2 ≤ -4 * (96 / 145 : ℝ) ^ 2 ∨
      reflectedPairBlockDet
          (criticalEvaluation (xiSpectralPoint q.1)
            (abs_xiSpectralPoint_im_lt_half q.1)
            (criticalFeature (t : ℂ) (by norm_num)))
          (criticalEvaluation (xiSpectralPoint q.1)
            (abs_xiSpectralPoint_im_lt_half q.1)
            (criticalFeature ((t - 1 : ℝ) : ℂ) (by norm_num))) /
        (xiSpectralPoint q.1).im ^ 2 ≤ -4 * (96 / 145 : ℝ) ^ 2 := by
  dsimp only
  have hy : (xiSpectralPoint q.1).im ≠ 0 := by
    have hrel : -(xiSpectralPoint q.1).im = (xiRightCenteredZero q).re := by
      rw [xiRightCenteredZero]
      simp [Complex.mul_re]
    intro hy0
    have hpos := xiRightCenteredZero_re_pos q
    rw [← hrel, hy0] at hpos
    linarith
  exact reflectedPairBlockDet_orientedAdjacentCriticalFeature_div_sq_le
    (((round (xiSpectralPoint q.1).re : ℤ) : ℝ))
    (abs_xiSpectralPoint_im_lt_half q.1) (abs_sub_round _) hy

/-- Nearest-integer fixed three-feature transverse energy charges every strict-right Xi copy by
the same rational quantum, independently of height and horizontal displacement. -/
theorem orientedAdjacentCriticalFeatureTransverseEnergy_xiRight_round_ge
    (q : XiRightZeroCopy) :
    (96 / 145 : ℝ) ^ 2 ≤
      orientedAdjacentCriticalFeatureTransverseEnergy
        (((round (xiSpectralPoint q.1).re : ℤ) : ℝ))
        (xiSpectralPoint q.1) (abs_xiSpectralPoint_im_lt_half q.1) := by
  have hy : (xiSpectralPoint q.1).im ≠ 0 := by
    have hrel : -(xiSpectralPoint q.1).im = (xiRightCenteredZero q).re := by
      rw [xiRightCenteredZero]
      simp [Complex.mul_re]
    intro hy0
    have hpos := xiRightCenteredZero_re_pos q
    rw [← hrel, hy0] at hpos
    linarith
  exact orientedAdjacentCriticalFeatureTransverseEnergy_ge _
    (abs_xiSpectralPoint_im_lt_half q.1) (abs_sub_round _) hy

/-- Finite multiplicity receiver for any packet whose transverse exterior energies carry the local
quantum. -/
theorem finite_multiplicity_mul_transverseQuantum_le_energy
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (E : ι → ℝ)
    (hE : ∀ i ∈ s, (96 / 145 : ℝ) ^ 2 ≤ E i) :
    (96 / 145 : ℝ) ^ 2 * ∑ i ∈ s, (m i : ℝ) ≤
      ∑ i ∈ s, (m i : ℝ) * E i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    (96 / 145 : ℝ) ^ 2 * (m i : ℝ) =
        (m i : ℝ) * (96 / 145 : ℝ) ^ 2 := by ring
    _ ≤ (m i : ℝ) * E i :=
      mul_le_mul_of_nonneg_left (hE i hi) (Nat.cast_nonneg _)

/-- Exact `75%` receiver for a source budget on the new transverse exterior-square charge. -/
theorem three_quarters_line_of_transverseExteriorEnergy
    {N N0 R E : ℝ} (hsplit : N = N0 + 2 * R)
    (hcharge : (96 / 145 : ℝ) ^ 2 * R ≤ E)
    (hbudget : (145 / 96 : ℝ) ^ 2 * E ≤ N / 8) :
    3 * N / 4 ≤ N0 := by
  have hreciprocal : R ≤ (145 / 96 : ℝ) ^ 2 * E := by
    calc
      R = (145 / 96 : ℝ) ^ 2 * ((96 / 145 : ℝ) ^ 2 * R) := by norm_num; ring
      _ ≤ (145 / 96 : ℝ) ^ 2 * E :=
        mul_le_mul_of_nonneg_left hcharge (sq_nonneg _)
  nlinarith

end

end RHTower
