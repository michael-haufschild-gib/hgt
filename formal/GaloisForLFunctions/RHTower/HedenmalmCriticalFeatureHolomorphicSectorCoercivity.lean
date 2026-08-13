import GaloisForLFunctions.RHTower.HedenmalmWardGreenCriticalFeatureTrace
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeaturePrimeGammaDecomposition

/-!
# Holomorphic-sector coercivity of the Hedenmalm critical feature

Off the critical line, a Weil diagonal is holomorphic: it contains `F(z)^2`, not the Hermitian
energy `|F(z)|^2`.  For a generic test this distinction prevents a source formula from bounding
same-copy energy.  The real-centered Hedenmalm critical feature lies in a uniformly acute sector
throughout the whole critical strip.  Its holomorphic square therefore controls half its Hermitian
energy pointwise.

Summing this inequality converts the existing four-term absolute-Euler prime--Gamma polarization
into an unconditional arithmetic majorant for the singular Ward--Green trace.  This closes the
fixed-feature Hermitian/source comparison.  It does not assert the separate dyadic lattice budget
needed for a zero-density improvement.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- The complete critical-feature Cauchy test is the literal rational critical kernel. -/
theorem criticalFeatureCauchyKernelTest_eq
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    criticalFeatureCauchyKernelTest t z =
      2 / (1 + (z - (t : ℂ)) ^ 2) := by
  unfold criticalFeatureCauchyKernelTest
  rw [← criticalEvaluation_realCriticalFeature_eq_hardyCauchySum t hz]
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  simp

/-- Real coefficients make the critical-feature kernel fixed by the Weil sharp involution. -/
theorem xiWeilSharp_criticalFeatureCauchyKernelTest (t : ℝ) :
    xiWeilSharp (criticalFeatureCauchyKernelTest t) =
      criticalFeatureCauchyKernelTest t := by
  funext z
  simp [xiWeilSharp, criticalFeatureCauchyKernelTest,
    criticalHardyLowerCauchyTest, criticalHardyUpperCauchyTest,
    xiWeilCauchyTest]
  ring

/-- Exact algebraic sector factorization for the critical-feature denominator. -/
theorem criticalFeatureDenominator_sector_factorization (x y : ℝ) :
    (1 + x ^ 2 - y ^ 2) ^ 2 - 3 * (2 * x * y) ^ 2 =
      (x ^ 2 - (1 - y ^ 2)) ^ 2 +
        4 * x ^ 2 * (1 - 4 * y ^ 2) := by
  ring

/-- **Critical-strip sector coercivity.**  The real part of the holomorphic square of every
real-centered critical feature controls half of its same-copy Hermitian energy. -/
theorem half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    (1 / 2 : ℝ) * Complex.normSq (criticalFeatureCauchyKernelTest t z) ≤
      ((criticalFeatureCauchyKernelTest t z) ^ 2).re := by
  let x : ℝ := z.re - t
  let y : ℝ := z.im
  let A : ℝ := 1 + x ^ 2 - y ^ 2
  let B : ℝ := 2 * x * y
  let D : ℝ := A ^ 2 + B ^ 2
  have hy2 : y ^ 2 < 1 / 4 := by
    have hsq := (sq_lt_sq₀ (abs_nonneg y)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by simpa [y] using hz)
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have hfour : 0 ≤ 1 - 4 * y ^ 2 := by linarith
  have hsector : 3 * B ^ 2 ≤ A ^ 2 := by
    have hid : A ^ 2 - 3 * B ^ 2 =
        (x ^ 2 - (1 - y ^ 2)) ^ 2 +
          4 * x ^ 2 * (1 - 4 * y ^ 2) := by
      simpa only [A, B] using criticalFeatureDenominator_sector_factorization x y
    have hright : 0 ≤
        (x ^ 2 - (1 - y ^ 2)) ^ 2 +
          4 * x ^ 2 * (1 - 4 * y ^ 2) := by positivity
    linarith
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hApos, sq_nonneg B]
  have hden : Complex.normSq (1 + (z - (t : ℂ)) ^ 2) = D := by
    dsimp [D, A, B, x, y]
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re]
    ring
  have hre :
      ((2 / (1 + (z - (t : ℂ)) ^ 2)) ^ 2).re =
        4 * (A ^ 2 - B ^ 2) / D ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im]
    norm_num
    rw [hden]
    have hreDen : ((z - (t : ℂ)) ^ 2).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ 2).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    field_simp [ne_of_gt hDpos]
    ring
  have hnorm :
      Complex.normSq (2 / (1 + (z - (t : ℂ)) ^ 2)) = 4 / D := by
    rw [Complex.normSq_div]
    norm_num [Complex.normSq_apply]
    have hreDen : ((z - (t : ℂ)) ^ 2).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ 2).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    ring
  rw [criticalFeatureCauchyKernelTest_eq t hz, hre, hnorm]
  field_simp [ne_of_gt hDpos]
  nlinarith

/-- Same-copy Hermitian energy of one fixed real-centered critical-feature channel. -/
def criticalFeatureHermitianEnergyTrace (t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy,
    Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))

/-- Fixed-feature Hermitian energy is absolutely summable on the multiplicity-exact Xi divisor. -/
theorem criticalFeatureHermitianEnergy_summable (t : ℝ) :
    Summable (fun q : XiZeroCopy =>
      Complex.normSq (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))) := by
  have hF := criticalFeatureCauchyKernelTest_squareSummable t
  rw [XiWeilSquareSummable] at hF
  simpa only [Complex.normSq_eq_norm_sq] using hF

/-- The Hermitian energy trace is nonnegative. -/
theorem criticalFeatureHermitianEnergyTrace_nonneg (t : ℝ) :
    0 ≤ criticalFeatureHermitianEnergyTrace t := by
  rw [criticalFeatureHermitianEnergyTrace]
  exact tsum_nonneg fun q => Complex.normSq_nonneg _

/-- **Hermitian-to-holomorphic trace comparison.**  Twice the real Weil polarization controls the
complete same-copy critical-feature energy, without RH. -/
theorem criticalFeatureHermitianEnergyTrace_le_two_re_xiWeilPolarization (t : ℝ) :
    criticalFeatureHermitianEnergyTrace t ≤
      2 * (xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest t)).re := by
  let F : ℂ → ℂ := criticalFeatureCauchyKernelTest t
  have hF : Summable (fun q : XiZeroCopy => ‖F (xiSpectralPoint q)‖ ^ 2) := by
    exact criticalFeatureCauchyKernelTest_squareSummable t
  have hnormSq : Summable (fun q : XiZeroCopy =>
      Complex.normSq (F (xiSpectralPoint q))) := by
    simpa only [Complex.normSq_eq_norm_sq] using hF
  have hsquareNorm : Summable (fun q : XiZeroCopy =>
      ‖(F (xiSpectralPoint q)) ^ 2‖) := by
    simpa only [norm_pow] using hF
  have hsquare : Summable (fun q : XiZeroCopy =>
      (F (xiSpectralPoint q)) ^ 2) :=
    summable_norm_iff.mp hsquareNorm
  have hre : Summable (fun q : XiZeroCopy =>
      ((F (xiSpectralPoint q)) ^ 2).re) := by
    refine (hsquare.map Complex.reCLM Complex.reCLM.continuous).congr ?_
    intro q
    rfl
  have htwoRe : Summable (fun q : XiZeroCopy =>
      2 * ((F (xiSpectralPoint q)) ^ 2).re) := hre.mul_left 2
  have hpoint (q : XiZeroCopy) :
      Complex.normSq (F (xiSpectralPoint q)) ≤
        2 * ((F (xiSpectralPoint q)) ^ 2).re := by
    have hsector := half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq t
      (abs_xiSpectralPoint_im_lt_half q)
    dsimp only [F]
    nlinarith
  have hsum := hnormSq.tsum_le_tsum hpoint htwoRe
  calc
    criticalFeatureHermitianEnergyTrace t =
        ∑' q : XiZeroCopy, Complex.normSq (F (xiSpectralPoint q)) := by
      rfl
    _ ≤ ∑' q : XiZeroCopy, 2 * ((F (xiSpectralPoint q)) ^ 2).re := hsum
    _ = 2 * (∑' q : XiZeroCopy, ((F (xiSpectralPoint q)) ^ 2).re) := by
      rw [tsum_mul_left]
    _ = 2 * (∑' q : XiZeroCopy, (F (xiSpectralPoint q)) ^ 2).re := by
      rw [Complex.re_tsum hsquare]
    _ = 2 * (xiWeilPolarization F F).re := by
      unfold xiWeilPolarization
      rw [show xiWeilSharp F = F by
        simpa only [F] using xiWeilSharp_criticalFeatureCauchyKernelTest t]
      congr 2
      apply tsum_congr
      intro q
      ring
    _ = 2 * (xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest t)).re := rfl

/-- Explicit four-term absolute-Euler prime--Gamma diagonal of the critical feature. -/
def criticalFeaturePrimeGammaSourceDiagonal (t : ℝ) : ℂ :=
  criticalHardyLowerLowerPrimeArchSource t t +
    criticalHardyPrimeGammaSourceCup t t +
    (starRingEnd ℂ) (criticalHardyPrimeGammaSourceCup t t) +
    criticalHardyUpperUpperPrimeArchSource t t

/-- The four-term source diagonal is exactly the multiplicity-exact Xi Weil polarization. -/
theorem xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal (t : ℝ) :
    xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest t) =
      criticalFeaturePrimeGammaSourceDiagonal t := by
  exact xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_primeGammaSource t t

/-- The explicit four-term prime--Gamma diagonal has nonnegative real part unconditionally. -/
theorem criticalFeaturePrimeGammaSourceDiagonal_re_nonneg (t : ℝ) :
    0 ≤ (criticalFeaturePrimeGammaSourceDiagonal t).re := by
  have henergy := criticalFeatureHermitianEnergyTrace_nonneg t
  have hle := criticalFeatureHermitianEnergyTrace_le_two_re_xiWeilPolarization t
  rw [xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal] at hle
  linarith

theorem fiveShiftWardGreenUpperConstant_nonneg :
    0 ≤ fiveShiftWardGreenUpperConstant := by
  rw [fiveShiftWardGreenUpperConstant]
  positivity

/-- **Arithmetic Ward--Green majorant.**  The singular same-copy Hermitian trace is bounded by
the explicit four-term absolute-Euler prime--Gamma critical-feature diagonal. -/
theorem fiveShiftCriticalFeatureWardGreenTrace_le_primeGammaSourceDiagonal (t : ℝ) :
    fiveShiftCriticalFeatureWardGreenTrace t ≤
      2 * fiveShiftWardGreenUpperConstant *
        (criticalFeaturePrimeGammaSourceDiagonal t).re := by
  let H : ℝ := criticalFeatureHermitianEnergyTrace t
  have hmajorSum : Summable (fun q : XiZeroCopy =>
      fiveShiftWardGreenUpperConstant *
        Complex.normSq
          (HedenmalmThetaSource.criticalEvaluation
            (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
            (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)))) := by
    refine ((criticalFeatureHermitianEnergy_summable t).mul_left
      fiveShiftWardGreenUpperConstant).congr ?_
    intro q
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
    rfl
  have htrace : fiveShiftCriticalFeatureWardGreenTrace t ≤
      fiveShiftWardGreenUpperConstant * H := by
    rw [fiveShiftCriticalFeatureWardGreenTrace]
    have hle := (fiveShiftCriticalFeatureWardGreenCurrent_summable t).tsum_le_tsum
      (fiveShiftCriticalFeatureWardGreenCurrent_le t) hmajorSum
    calc
      (∑' q : XiZeroCopy, fiveShiftCriticalFeatureWardGreenCurrent t q) ≤
          ∑' q : XiZeroCopy,
            fiveShiftWardGreenUpperConstant *
              Complex.normSq
                (HedenmalmThetaSource.criticalEvaluation
                  (xiSpectralPoint q) (abs_xiSpectralPoint_im_lt_half q)
                  (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num))) := hle
      _ = ∑' q : XiZeroCopy,
            fiveShiftWardGreenUpperConstant *
              Complex.normSq
                (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
        apply tsum_congr
        intro q
        rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
        rfl
      _ = fiveShiftWardGreenUpperConstant * H := by
        rw [tsum_mul_left]
        rfl
  have hH := criticalFeatureHermitianEnergyTrace_le_two_re_xiWeilPolarization t
  rw [xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal] at hH
  calc
    fiveShiftCriticalFeatureWardGreenTrace t ≤
        fiveShiftWardGreenUpperConstant * H := htrace
    _ ≤ fiveShiftWardGreenUpperConstant *
        (2 * (criticalFeaturePrimeGammaSourceDiagonal t).re) :=
      mul_le_mul_of_nonneg_left hH fiveShiftWardGreenUpperConstant_nonneg
    _ = 2 * fiveShiftWardGreenUpperConstant *
        (criticalFeaturePrimeGammaSourceDiagonal t).re := by ring

end

end RHTower
