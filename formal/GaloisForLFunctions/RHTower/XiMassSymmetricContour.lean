import GaloisForLFunctions.RHTower.XiMassFiniteContour
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour

/-!
# Symmetric Euler-line contour for the Xi mass test

The analytic mass test is even and the centered Xi logarithmic derivative is odd.  A symmetric
rectangle therefore folds to twice its bottom Euler edge plus one right vertical edge.  When the
rectangle lies inside the mass branch strip and avoids Xi zeros vertically, this folded expression
is exactly the finite multiplicity-copy mass trace.
-/

open Complex Function intervalIntegral Set

namespace RHTower

noncomputable section

/-- Even mass test times odd centered Xi logarithmic derivative is odd. -/
theorem xiMassLogDerivIntegrand_neg (a : ℝ) (τ z : ℂ) :
    xiMassAnalyticTest a τ (-z) * logDeriv XiC (-z) =
      -(xiMassAnalyticTest a τ z * logDeriv XiC z) := by
  rw [xiMassAnalyticTest_neg, logDeriv_XiC_neg]
  ring

/-- Symmetric contour reduction for the analytic Xi mass test. -/
theorem rectIntegral_xiMassLogDeriv_symmetric (a : ℝ) (τ : ℂ) (R c : ℝ) :
    rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * ((∫ x in -R..R,
          xiMassAnalyticTest a τ ((x : ℂ) - c * I) *
            logDeriv XiC ((x : ℂ) - c * I)) +
        I • (∫ y in -c..c,
          xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I))) := by
  exact rectIntegral_symmetric_eq_two_bottom_add_vertical
    (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z)
    (xiMassLogDerivIntegrand_neg a τ) R c

/-- Exact finite mass trace on a symmetric branch-strip rectangle.  Horizontal nonvanishing is
automatic beyond the centered Xi zero strip; only the two vertical edges need be selected away
from zeros. -/
theorem rectIntegral_xiMassLogDeriv_symmetric_eq_xiZeroCopyClosedRectangleSum
    {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ)
    (hright : ∀ y ∈ uIcc (-c) c, XiC ((R : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-c) c, XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I) =
      2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassAnalyticTest a τ (xiSpectralPoint q) := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
  let z₂ : ℂ := (((R : ℝ) : ℂ) + c * I)
  have hz₁re : z₁.re = -R := by simp [z₁, Complex.mul_re]
  have hz₁im : z₁.im = -c := by simp [z₁, Complex.mul_im]
  have hz₂re : z₂.re = R := by simp [z₂, Complex.mul_re]
  have hz₂im : z₂.im = c := by simp [z₂, Complex.mul_im]
  have hre : z₁.re < z₂.re := by rw [hz₁re, hz₂re]; linarith
  have him : z₁.im < z₂.im := by rw [hz₁im, hz₂im]; linarith
  have hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a := by
    intro z hz
    have hzim := (Complex.mem_reProdIm.mp hz).2
    rw [hz₁im, hz₂im, uIcc_of_le (by linarith : -c ≤ c)] at hzim
    obtain ⟨hzim_lo, hzim_hi⟩ := hzim
    change |z.im| < a
    rw [abs_lt]
    constructor <;> linarith
  have hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiC ((x : ℂ) + z₁.im * I) ≠ 0 := by
    intro x _ hzero
    have hz := xiC_zero_im_mem_openHalf hzero
    have hedge : (((x : ℂ) + z₁.im * I)).im = -c := by rw [hz₁im]; simp
    rw [hedge] at hz
    linarith
  have htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiC ((x : ℂ) + z₂.im * I) ≠ 0 := by
    intro x _ hzero
    have hz := xiC_zero_im_mem_openHalf hzero
    have hedge : (((x : ℂ) + z₂.im * I)).im = c := by rw [hz₂im]; simp
    rw [hedge] at hz
    linarith
  have hright' : ∀ y ∈ uIcc z₁.im z₂.im,
      XiC ((z₂.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im] at hy
    simpa only [hz₂re] using hright y hy
  have hleft' : ∀ y ∈ uIcc z₁.im z₂.im,
      XiC ((z₁.re : ℂ) + y * I) ≠ 0 := by
    intro y hy
    rw [hz₁im, hz₂im] at hy
    simpa only [hz₁re, Complex.ofReal_neg] using hleft y hy
  change rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z) z₁ z₂ =
    2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
      xiMassAnalyticTest a τ (xiSpectralPoint q)
  exact rectIntegral_xiMassAnalyticTest_mul_logDeriv_eq_xiZeroCopyClosedRectangleSum
    ha τ hre him hstrip hbot htop hright' hleft'

/-- On every symmetric mass rectangle, the exact finite copied spectral sum equals twice an honest
Euler-line bottom integral plus one vertical error integral. -/
theorem xiMassFiniteSpectralSum_eq_bottomPrimeArch_add_vertical
    {a c R : ℝ} (ha : 0 < a) (hhalf : 1 / 2 < c) (hca : c < a) (hR : 0 < R)
    (τ : ℂ)
    (hright : ∀ y ∈ uIcc (-c) c, XiC ((R : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-c) c, XiC (((-R : ℝ) : ℂ) + y * I) ≠ 0) :
    2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - c * I) (((R : ℝ) : ℂ) + c * I),
            xiMassAnalyticTest a τ (xiSpectralPoint q) =
      2 * ((∫ x in -R..R,
          xiMassAnalyticTest a τ ((x : ℂ) - c * I) *
            (-I *
              (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
                  (((1 / 2 + c : ℝ) : ℂ) + x * I) -
                logDeriv archFactor (((1 / 2 + c : ℝ) : ℂ) + x * I)))) +
        I • (∫ y in -c..c,
          xiMassAnalyticTest a τ ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I))) := by
  rw [← rectIntegral_xiMassLogDeriv_symmetric_eq_xiZeroCopyClosedRectangleSum
    ha hhalf hca hR τ hright hleft,
    rectIntegral_xiMassLogDeriv_symmetric]
  congr 2
  apply intervalIntegral.integral_congr
  intro x _
  change xiMassAnalyticTest a τ ((x : ℂ) - c * I) *
      logDeriv XiC ((x : ℂ) - c * I) = _
  rw [logDeriv_XiC_bottom_eq_primeArch hhalf x]

end

end RHTower
