import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeaturePrimeGammaDecomposition
import GaloisForLFunctions.RHTower.XiWardFiveShiftCriticalEvaluationLanding
import GaloisForLFunctions.RHTower.XiWardFiveShiftPairedSubmicroscopicSeparator

/-!
# Height-local critical-feature frame and singular five-shift quantum

The real-centered Hedenmalm critical features do more than separate points of the open critical
strip.  Their Cauchy kernel has an exact squared-modulus law.  Choosing the nearest integer to the
horizontal spectral coordinate gives a uniform lower frame bound `64 / 25`, independent of height
and transverse displacement.

Functional-equation pairing transports this bound to the five-shift Euler--Gamma separator.  After
the forced inverse-square transverse normalization, every strict-right Xi multiplicity copy carries
at least `64 / 2025` in one nearest-integer feature channel.  Thus height escape and reporter
degeneration are not the remaining obstruction.  What remains is a source-native trace realization
of the singular inverse-square channel.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Exact squared modulus of a real-centered critical-feature evaluation. -/
theorem normSq_criticalEvaluation_realCriticalFeature_eq
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    Complex.normSq
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num))) =
      4 /
        ((1 + (z.re - t) ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ) +
          (2 * (z.re - t) * z.im) ^ (2 : ℕ)) := by
  have hden :
      Complex.normSq (1 + (z - (t : ℂ)) ^ (2 : ℕ)) =
        (1 + (z.re - t) ^ (2 : ℕ) - z.im ^ (2 : ℕ)) ^ (2 : ℕ) +
          (2 * (z.re - t) * z.im) ^ (2 : ℕ) := by
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz,
    Complex.normSq_div]
  have hconj : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := by simp
  rw [hconj, hden]
  norm_num [Complex.normSq_apply]

/-- **Uniform nearest-center frame bound.** Every real critical feature whose center is within
one half-unit of a strip point's horizontal coordinate sees that point with energy at least
`64 / 25`. -/
theorem normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (64 / 25 : ℝ) ≤
      Complex.normSq
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num))) := by
  rw [normSq_criticalEvaluation_realCriticalFeature_eq t hz]
  let x : ℝ := z.re - t
  let y : ℝ := z.im
  let D : ℝ :=
    (1 + x ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * x * y) ^ (2 : ℕ)
  have hx2 : x ^ (2 : ℕ) ≤ 1 / 4 := by
    dsimp only [x]
    have hsq := (sq_le_sq₀ (abs_nonneg (z.re - t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 ht
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hyabs : |y| < 1 / 2 := by simpa only [y] using hz
  have hy2 : y ^ (2 : ℕ) < 1 / 4 := by
    have hsq := (sq_lt_sq₀ (abs_nonneg y)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hyabs
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hDid : D = (1 + x ^ (2 : ℕ) + y ^ (2 : ℕ)) ^ (2 : ℕ) - 4 * y ^ (2 : ℕ) := by
    dsimp only [D]
    ring
  have hbracket : -2 + 2 * x ^ (2 : ℕ) + y ^ (2 : ℕ) ≤ 0 := by linarith
  have hcorr : y ^ (2 : ℕ) * (-2 + 2 * x ^ (2 : ℕ) + y ^ (2 : ℕ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) hbracket
  have hbase0 : 0 ≤ 1 + x ^ (2 : ℕ) := by positivity
  have hbase : 1 + x ^ (2 : ℕ) ≤ 5 / 4 := by linarith
  have hbasesq : (1 + x ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (5 / 4 : ℝ) ^ (2 : ℕ) :=
    (sq_le_sq₀ hbase0 (by norm_num)).2 hbase
  have hDle : D ≤ 25 / 16 := by
    rw [hDid]
    nlinarith
  have hDpos : 0 < D := by
    have hfirst : 0 < 1 + x ^ (2 : ℕ) - y ^ (2 : ℕ) := by
      nlinarith [sq_nonneg x]
    have hfirstSq : 0 < (1 + x ^ (2 : ℕ) - y ^ (2 : ℕ)) ^ (2 : ℕ) :=
      sq_pos_of_pos hfirst
    dsimp only [D]
    nlinarith [sq_nonneg (2 * x * y)]
  change (64 / 25 : ℝ) ≤ 4 / D
  rw [le_div_iff₀ hDpos]
  nlinarith

/-- Conjugating the strip point preserves the evaluation energy of every real-centered feature. -/
theorem normSq_criticalEvaluation_realCriticalFeature_conj
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
    Complex.normSq
        (criticalEvaluation ((starRingEnd ℂ) z) hzc
          (criticalFeature (t : ℂ) (by norm_num))) =
      Complex.normSq
        (criticalEvaluation z hz
          (criticalFeature (t : ℂ) (by norm_num))) := by
  dsimp only
  rw [normSq_criticalEvaluation_realCriticalFeature_eq t (by simpa using hz),
    normSq_criticalEvaluation_realCriticalFeature_eq t hz]
  simp only [conj_im, conj_re]
  ring

/-- Singular functional-equation-paired five-shift current in one real critical-feature channel.
The inverse-square factor is forced by quadratic coalescence at the critical boundary. -/
def fiveShiftCriticalFeaturePairedRenormalizedCurrent
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) : ℝ :=
  let hzc : |((starRingEnd ℂ) z).im| < 1 / 2 := by simpa using hz
  (-z.im)⁻¹ ^ (2 : ℕ) *
    (-(fiveShiftCriticalEvaluationEnergyCurrent 1 (by norm_num) z hz
          (criticalFeature (t : ℂ) (by norm_num)) +
        fiveShiftCriticalEvaluationEnergyCurrent 1 (by norm_num)
          ((starRingEnd ℂ) z) hzc
          (criticalFeature (t : ℂ) (by norm_num))))

/-- Exact factorization of the paired critical-feature current into the scalar singular separator
and the nonsingular feature energy. -/
theorem fiveShiftCriticalFeaturePairedRenormalizedCurrent_eq
    (t : ℝ) (z : ℂ) (hz : |z.im| < 1 / 2) :
    fiveShiftCriticalFeaturePairedRenormalizedCurrent t z hz =
      fiveShiftEulerGammaPairedRenormalizedFeature 1 (-z.im) *
        Complex.normSq
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num))) := by
  rw [fiveShiftCriticalFeaturePairedRenormalizedCurrent]
  rw [fiveShiftCriticalEvaluationEnergyCurrent_eq,
    fiveShiftCriticalEvaluationEnergyCurrent_eq,
    normSq_criticalEvaluation_realCriticalFeature_conj t hz]
  simp only [conj_im, neg_neg]
  rw [fiveShiftEulerGammaPairedRenormalizedFeature,
    fiveShiftEulerGammaPairedFeature]
  ring

/-- Every critical-feature channel within one half-unit of a strict-right strip point carries a
uniform inverse-square-renormalized five-shift quantum. -/
theorem fiveShiftCriticalFeaturePairedRenormalizedCurrent_ge
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ha0 : 0 < -z.im) (ha : -z.im ≤ 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (64 / 2025 : ℝ) ≤
      fiveShiftCriticalFeaturePairedRenormalizedCurrent t z hz := by
  rw [fiveShiftCriticalFeaturePairedRenormalizedCurrent_eq]
  have hp := fiveShiftEulerGammaPairedRenormalizedFeature_one_ge ha0 ha
  have he :=
    normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half t hz ht
  calc
    (64 / 2025 : ℝ) = (1 / 81 : ℝ) * (64 / 25 : ℝ) := by norm_num
    _ ≤ fiveShiftEulerGammaPairedRenormalizedFeature 1 (-z.im) *
        (64 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_right hp (by norm_num)
    _ ≤ fiveShiftEulerGammaPairedRenormalizedFeature 1 (-z.im) *
        Complex.normSq
          (criticalEvaluation z hz
            (criticalFeature (t : ℂ) (by norm_num))) :=
      mul_le_mul_of_nonneg_left he (le_trans (by norm_num) hp)

/-- **Height-local Xi quantum.** The nearest integer-centered feature gives every strict-right Xi
multiplicity copy at least `64 / 2025` of singular paired five-shift charge.  The reporter is chosen
from one fixed countable family and the bound is independent of height and aperture. -/
theorem fiveShiftCriticalFeaturePairedRenormalizedCurrent_xiRightZeroCopy_round_ge
    (q : XiRightZeroCopy) :
    (64 / 2025 : ℝ) ≤
      fiveShiftCriticalFeaturePairedRenormalizedCurrent
        ((round (xiSpectralPoint q.1).re : ℤ) : ℝ)
        (xiSpectralPoint q.1) (abs_xiSpectralPoint_im_lt_half q.1) := by
  apply fiveShiftCriticalFeaturePairedRenormalizedCurrent_ge
  · rw [show -(xiSpectralPoint q.1).im = (xiRightCenteredZero q).re by
      rw [xiRightCenteredZero]
      simp [Complex.mul_re]]
    exact xiRightCenteredZero_re_pos q
  · rw [show -(xiSpectralPoint q.1).im = (xiRightCenteredZero q).re by
      rw [xiRightCenteredZero]
      simp [Complex.mul_re]]
    exact le_of_lt (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  · exact abs_sub_round _

end


end RHTower
