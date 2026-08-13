import GaloisForLFunctions.RHTower.XiGaussianArchimedeanEdge
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour

/-!
# Exact monomial Gaussian completed source formula

The prime and completed archimedean edge identities are assembled before taking real parts.  The
result is the literal Gaussian--Hermite completed source: Hardy Gamma integral plus crossed polar
mass minus the absolutely convergent critical half-density prime Fourier series.  The same source
is identified pointwise with the oriented bottom `Xi'/Xi` integrand.
-/

open Complex Filter MeasureTheory Set Topology intervalIntegral

namespace RHTower

noncomputable section

/-- Completed bottom source with the explicit-formula orientation `archimedean - prime`. -/
def xiGaussianCompletedBottomSource
    (t : ℝ) (k : ℕ) (c x : ℝ) : ℂ :=
  xiGaussianBottomArchIntegrand t k c x -
    xiGaussianBottomPrimeIntegrand t k c x

/-- Gaussian bottom logarithmic-derivative integrand of the centered Xi function. -/
def xiGaussianBottomXiLogIntegrand
    (t : ℝ) (k : ℕ) (c x : ℝ) : ℂ :=
  xiGaussianTestC t k ((x : ℂ) - c * I) *
    logDeriv XiC ((x : ℂ) - c * I)

/-- The explicit completed source is exactly the oriented bottom Xi logarithmic derivative. -/
theorem xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog
    {c : ℝ} (hc : 1 / 2 < c) (t : ℝ) (k : ℕ) (x : ℝ) :
    xiGaussianCompletedBottomSource t k c x =
      -I * xiGaussianBottomXiLogIntegrand t k c x := by
  rw [xiGaussianCompletedBottomSource, xiGaussianBottomXiLogIntegrand,
    xiGaussianBottomArchIntegrand, xiGaussianArchHorizontalIntegrand,
    xiGaussianBottomPrimeIntegrand,
    logDeriv_XiC_bottom_eq_primeArch hc x]
  have hpoint :
      xiMassCenteredArchPoint ((x : ℂ) + ((-c : ℝ) : ℂ) * I) =
        xiMassBottomEulerPoint c x := by
    unfold xiMassCenteredArchPoint xiMassBottomEulerPoint
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [hpoint]
  have hcoord :
      (((1 / 2 + c : ℝ) : ℂ) + x * I) = xiMassBottomEulerPoint c x := by rfl
  rw [hcoord]
  have htest :
      ((x : ℂ) + ((-c : ℝ) : ℂ) * I) = (x : ℂ) - c * I := by
    push_cast
    ring
  rw [htest]
  ring_nf
  rw [I_sq]
  ring

/-- Absolute integrability of the full Gaussian von-Mangoldt bottom edge. -/
theorem integrable_xiGaussianBottomPrimeIntegrand
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    Integrable (xiGaussianBottomPrimeIntegrand t k c) := by
  let B : ℝ := xiMassBottomVonMangoldtBound c
  have hprofile : Integrable (fun x : ℝ =>
      xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)) := by
    simpa [sub_eq_add_neg] using integrable_xiGaussianTestC_horizontal ht k (-c)
  have hmajor : Integrable (fun x : ℝ =>
      |B| * ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖) :=
    hprofile.norm.const_mul |B|
  have hcont : Continuous (xiGaussianBottomPrimeIntegrand t k c) := by
    have htest : Continuous (fun x : ℝ =>
        xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)) := by
      unfold xiGaussianTestC
      fun_prop
    exact htest.mul (continuous_xiMassBottomVonMangoldtLSeries hc)
  refine hmajor.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hL := norm_xiMassBottomVonMangoldtLSeries_le (x := x) hc
  have hB : B ≤ |B| := le_abs_self B
  rw [xiGaussianBottomPrimeIntegrand, norm_mul]
  calc
    ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ *
        ‖LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
          (xiMassBottomEulerPoint c x)‖ ≤
      ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ * B :=
        mul_le_mul_of_nonneg_left hL (norm_nonneg _)
    _ ≤ ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ * |B| :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = |B| * ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ := by ring

theorem integrable_xiGaussianCompletedBottomSource
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    Integrable (xiGaussianCompletedBottomSource t k c) := by
  have harch : Integrable (xiGaussianBottomArchIntegrand t k c) := by
    exact integrable_xiGaussianArchHorizontalIntegrand ht hc k
      (y := -c) ⟨le_rfl, by linarith⟩ (by linarith)
  exact harch.sub (integrable_xiGaussianBottomPrimeIntegrand ht hc k)

/-- Exact complex monomial completed-source formula. -/
theorem integral_xiGaussianCompletedBottomSource_eq
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianCompletedBottomSource t k c x) =
      (∫ x : ℝ, xiGaussianCenteredArchIntegrand t k x) +
        2 * Real.pi * xiGaussianTestC t k xiMassArchPole -
          ∑' n : ℕ, xiGaussianCenteredPrimeAtom t k n := by
  have harch : Integrable (xiGaussianBottomArchIntegrand t k c) := by
    exact integrable_xiGaussianArchHorizontalIntegrand ht hc k
      (y := -c) ⟨le_rfl, by linarith⟩ (by linarith)
  have hprime := integrable_xiGaussianBottomPrimeIntegrand ht hc k
  change (∫ x : ℝ, xiGaussianBottomArchIntegrand t k c x -
    xiGaussianBottomPrimeIntegrand t k c x) = _
  rw [integral_sub harch hprime,
    integral_xiGaussianBottomArch_eq_centered_add_residue ht hc k,
    integral_xiGaussianBottomPrimeIntegrand_eq_tsum_centered ht hc k]

/-- Exact real monomial prime--Gamma formula. -/
theorem re_integral_xiGaussianCompletedBottomSource_eq
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianCompletedBottomSource t k c x).re =
      (∫ x : ℝ, xiGaussianHermiteProfile t k x * gammaHardyPhaseRate x) +
        2 * Real.pi * ((-(1 / 4 : ℝ)) ^ k * Real.exp (t / 4)) -
          (∑' n : ℕ, xiGaussianCenteredPrimeAtom t k n).re := by
  have h := integral_xiGaussianCompletedBottomSource_eq ht hc k
  have hre := congrArg Complex.re h
  rw [Complex.sub_re, Complex.add_re, Complex.mul_re,
    re_integral_xiGaussianCenteredArch_eq_gammaHardyPhaseRate ht hc k] at hre
  have hscalarRe : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by norm_num
  have hscalarIm : (2 * (Real.pi : ℂ)).im = 0 := by norm_num
  rw [hscalarRe, hscalarIm, zero_mul, sub_zero,
    re_xiGaussianTestC_archPole] at hre
  exact hre

/-- The bottom Xi logarithmic-derivative integrand is absolutely integrable for every legal
Gaussian test and Euler depth. -/
theorem integrable_xiGaussianBottomXiLogIntegrand
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    Integrable (xiGaussianBottomXiLogIntegrand t k c) := by
  have hsource := integrable_xiGaussianCompletedBottomSource ht hc k
  have heq : xiGaussianBottomXiLogIntegrand t k c =
      fun x => I * xiGaussianCompletedBottomSource t k c x := by
    funext x
    have h := xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog hc t k x
    have hIi : I * (-I) = (1 : ℂ) := by
      rw [mul_neg, Complex.I_mul_I]
      norm_num
    calc
      xiGaussianBottomXiLogIntegrand t k c x =
          I * (-I * xiGaussianBottomXiLogIntegrand t k c x) := by
        rw [← mul_assoc, hIi, one_mul]
      _ = I * xiGaussianCompletedBottomSource t k c x := by rw [h]
  rw [heq]
  exact hsource.const_mul I

/-- Integrated source/Xi orientation identity. -/
theorem integral_xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianCompletedBottomSource t k c x) =
      -I * ∫ x : ℝ, xiGaussianBottomXiLogIntegrand t k c x := by
  have hxi := integrable_xiGaussianBottomXiLogIntegrand ht hc k
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact xiGaussianCompletedBottomSource_eq_neg_I_mul_XiLog hc t k x

end

end RHTower
