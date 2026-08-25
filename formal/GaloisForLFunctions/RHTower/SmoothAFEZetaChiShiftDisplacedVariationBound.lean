import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDisplacedGlobalDerivativeBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualQuarterHeightDerivative

/-!
# Conductor-scale variation of displaced chi ratios

The two logarithmic chi slopes on a moving Levinson line are differences of
digamma values whose real parts stay in `[1/8, 3/8]`.  Trigamma mean-value
bounds therefore retain the conductor saving `1/tau`, uniformly in the
displacement parameters used below.
-/

noncomputable section

open Complex Set

namespace RHTower

/-- Two positive-height digamma points with real parts in `[1/8,3/8]`
differ by `O((1+|v|)/tau)`. -/
theorem norm_digamma_positive_conductor_two_strip_le
    {tau v a b : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau)
    (haLow : 1 / 8 ≤ a) (haHigh : a ≤ 3 / 8)
    (hbLow : 1 / 8 ≤ b) (hbHigh : b ≤ 3 / 8) :
    ‖Complex.digamma
        ((a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) -
      Complex.digamma
        ((b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let z : ℂ := Complex.digamma
    (((1 / 4 : ℝ) : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)
  have ha := norm_digamma_positive_conductor_increment_quarter_le
    htau hv haLow haHigh
  have hvzero : 2 * |(0 : ℝ)| ≤ tau := by simp; linarith
  have hb0 := norm_digamma_positive_conductor_increment_quarter_le
    (tau := tau) (v := 0) htau hvzero hbLow hbHigh
  have hb :
      ‖z - Complex.digamma
          ((b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
        (16 / tau ^ 2 + 2 * Real.pi / tau) := by
    rw [norm_sub_rev]
    simpa only [z, sub_zero, abs_zero, add_zero, one_mul, mul_one] using hb0
  have hq : 1 ≤ 1 + |v| := by linarith [abs_nonneg v]
  have hbase : 0 ≤ 16 / tau ^ 2 + 2 * Real.pi / tau := by positivity
  calc
    ‖Complex.digamma
          ((a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) -
        Complex.digamma
          ((b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ =
        ‖(Complex.digamma
            ((a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) - z) +
          (z - Complex.digamma
            ((b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I))‖ := by
          congr 1
          ring
    _ ≤ ‖Complex.digamma
            ((a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I) - z‖ +
          ‖z - Complex.digamma
            ((b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) +
          (16 / tau ^ 2 + 2 * Real.pi / tau) := by
          exact add_le_add (by simpa only [z] using ha) hb
    _ ≤ (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) +
          (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
          have hbaseq :
              16 / tau ^ 2 + 2 * Real.pi / tau ≤
                (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hq hbase)
          exact add_le_add (le_refl _) hbaseq
    _ = 2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by ring

/-- Conjugate lower-height form of the two-strip conductor increment. -/
theorem norm_digamma_negative_conductor_two_strip_le
    {tau v a b : ℝ} (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau)
    (haLow : 1 / 8 ≤ a) (haHigh : a ≤ 3 / 8)
    (hbLow : 1 / 8 ≤ b) (hbHigh : b ≤ 3 / 8) :
    ‖Complex.digamma
        ((a : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I) -
      Complex.digamma
        ((b : ℂ) - ((tau / 2 : ℝ) : ℂ) * I)‖ ≤
      2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  let A : ℂ := (a : ℂ) + (((tau - v) / 2 : ℝ) : ℂ) * I
  let B : ℂ := (b : ℂ) + ((tau / 2 : ℝ) : ℂ) * I
  have hA : (starRingEnd ℂ) A =
      (a : ℂ) - (((tau - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [A, map_div₀, map_ofNat]
  have hB : (starRingEnd ℂ) B =
      (b : ℂ) - ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [B, map_div₀, map_ofNat]
  rw [← hA, ← hB, ReflectedDigammaAnomaly.digamma_conj,
    ReflectedDigammaAnomaly.digamma_conj,
    ← map_sub, norm_conj]
  exact norm_digamma_positive_conductor_two_strip_le
    htau hv haLow haHigh hbLow hbHigh

/-- Exact conductor-window saving for the displaced chi logarithmic slope. -/
theorem norm_logDeriv_zetaChi_displaced_neg_shift_sub_le
    {d eta tau v : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖logDeriv zetaChi
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (displacedLinePt d tau)‖ ≤
      2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
  have hdhalf : d < 1 / 2 := by linarith
  have hetaHalf : eta < 1 / 2 := by linarith
  rw [logDeriv_zetaChi_displaced_neg_shift_sub_eq_digamma_increments
    hd hdhalf heta hetaHalf]
  let A : ℂ := Complex.digamma
    ((displacedLinePt d tau -
      (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2)
  let B : ℂ := Complex.digamma (displacedLinePt d tau / 2)
  let C : ℂ := Complex.digamma
    ((1 - (displacedLinePt d tau -
      (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2)
  let E : ℂ := Complex.digamma ((1 - displacedLinePt d tau) / 2)
  have hAarg :
      (displacedLinePt d tau -
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) / 2 =
        ((1 / 4 + eta / 2 : ℝ) : ℂ) +
          (((tau - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
      ring
    · norm_num [displacedLinePt]
  have hBarg : displacedLinePt d tau / 2 =
      ((1 / 4 - d / 2 : ℝ) : ℂ) +
        ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
      ring
    · norm_num [displacedLinePt]
  have hCarg :
      (1 - (displacedLinePt d tau -
        (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I))) / 2 =
        ((1 / 4 - eta / 2 : ℝ) : ℂ) -
          (((tau - v) / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
      ring
    · norm_num [displacedLinePt]
      ring
  have hEarg : (1 - displacedLinePt d tau) / 2 =
      ((1 / 4 + d / 2 : ℝ) : ℂ) -
        ((tau / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · norm_num [displacedLinePt]
      ring
    · norm_num [displacedLinePt]
      ring
  have hAB : ‖A - B‖ ≤
      2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
    dsimp only [A, B]
    rw [hAarg, hBarg]
    exact norm_digamma_positive_conductor_two_strip_le htau hv
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hCE : ‖C - E‖ ≤
      2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by
    dsimp only [C, E]
    rw [hCarg, hEarg]
    exact norm_digamma_negative_conductor_two_strip_le htau hv
      (by linarith) (by linarith) (by linarith) (by linarith)
  change ‖-(A - B) / 2 - (C - E) / 2‖ ≤ _
  calc
    ‖-(A - B) / 2 - (C - E) / 2‖
        ≤ ‖-(A - B) / 2‖ + ‖(C - E) / 2‖ := norm_sub_le _ _
    _ = ‖A - B‖ / 2 + ‖C - E‖ / 2 := by
      rw [norm_div, norm_neg, norm_div]
      norm_num
    _ ≤ (2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)) / 2 +
          (2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)) / 2 := by
      gcongr
    _ = 2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|) := by ring

/-- Integration-friendly displaced slow-variation bound. -/
theorem norm_logDeriv_zetaChi_displaced_neg_shift_sub_le_coarse
    {d eta tau v : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (htau : 4 ≤ tau) (hv : 2 * |v| ≤ tau) :
    ‖logDeriv zetaChi
        (displacedLinePt d tau -
          (((-(d + eta) : ℝ) : ℂ) + (v : ℂ) * I)) -
      logDeriv zetaChi (displacedLinePt d tau)‖ ≤
      (8 + 4 * Real.pi) * (1 + |v|) / tau := by
  have h := norm_logDeriv_zetaChi_displaced_neg_shift_sub_le
    hd hdquarter heta hetaquarter htau hv
  have htau0 : 0 < tau := by linarith
  have hpow : 16 / tau ^ 2 ≤ 4 / tau := by
    rw [div_le_div_iff₀ (sq_pos_of_pos htau0) htau0]
    nlinarith
  refine h.trans ?_
  calc
    2 * (16 / tau ^ 2 + 2 * Real.pi / tau) * (1 + |v|)
        ≤ 2 * (4 / tau + 2 * Real.pi / tau) * (1 + |v|) := by gcongr
    _ = (8 + 4 * Real.pi) * (1 + |v|) / tau := by
      field_simp
      ring

end RHTower
