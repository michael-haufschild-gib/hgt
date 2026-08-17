import GaloisForLFunctions.RHTower.XiMassJetSourceSide
import GaloisForLFunctions.RHTower.XiMassPolynomialEulerContourSourceIdentity

/-!
# The caustic-null jet is a polynomial filter

Along the dispersion relation the jet multiplier is `(z² + 4a⁴)^{2N}`, the square of the real
polynomial `(X + 4a⁴)^N` evaluated at `z²`.  The jet-modified analytic test is therefore literally a
polynomial-filtered mass test, so the polynomial-filtered Euler-contour source identity applies to
it verbatim: the weighted trace of the jet is the normalized absolutely convergent von-Mangoldt
minus archimedean bottom integral of the modified receiver.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- The caustic-null jet written as a real polynomial in the squared spatial frequency. -/
def xiMassJetPoly (a : ℝ) (N : ℕ) : Polynomial ℝ :=
  (Polynomial.X + Polynomial.C (4 * a ^ 4)) ^ N

theorem evalRealPolynomial_xiMassJetPoly (a : ℝ) (N : ℕ) (w : ℂ) :
    evalRealPolynomial (xiMassJetPoly a N) w = (w + ((4 * a ^ 4 : ℝ) : ℂ)) ^ N := by
  rw [xiMassJetPoly, evalRealPolynomial]
  simp

/-- **The jet-modified test is the polynomial-filtered test of `(X + 4a⁴)^N`.** -/
theorem xiMassJetAnalyticTest_eq_poly {a : ℝ} (ha : 1 / 2 < a) (N : ℕ) (τ z : ℂ) :
    xiMassJetAnalyticTest a N τ z = xiMassPolyAnalyticTest (xiMassJetPoly a N) a τ z := by
  have hfreq : (a ^ 2 : ℝ) + xiMassCausticFrequency a ^ 2 = 4 * a ^ 4 := by
    rw [xiMassCausticFrequency_sq ha]
    ring
  have hbase : z ^ 2 + ((a ^ 2 : ℝ) : ℂ) + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2
      = z ^ 2 + ((4 * a ^ 4 : ℝ) : ℂ) := by
    have hc : ((a ^ 2 : ℝ) : ℂ) + ((xiMassCausticFrequency a : ℝ) : ℂ) ^ 2
        = ((4 * a ^ 4 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_add, hfreq]
    linear_combination hc
  have hjet : xiMassCausticJet a N (xiMassAnalyticSqrt a z)
      = (z ^ 2 + ((4 * a ^ 4 : ℝ) : ℂ)) ^ (2 * N) := by
    rw [xiMassCausticJet, xiMassAnalyticSqrt_sq, xiMassAnalyticArg, hbase]
  rw [xiMassJetAnalyticTest, xiMassPolyAnalyticTest, hjet,
    evalRealPolynomial_xiMassJetPoly, ← pow_mul]
  congr 2
  ring

/-- **(22.5) The jet Euler-contour source identity.**  The jet-weighted mass trace is the
normalized absolutely convergent von-Mangoldt minus archimedean bottom integral of the
jet-modified receiver. -/
theorem traceWC_xiMassCausticJet_eq_normalizedBottomEulerContour {a c : ℝ} (ha : 1 / 2 < a)
    (N : ℕ) (hhalf : 1 / 2 < c) (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) :
    (xiMassFamily ha.le).traceWC (xiMassCausticJetWeight ha N) τ
      = normalizedXiMassPolyBottomEulerContour (xiMassJetPoly a N) a c τ := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hsum : Summable (fun q : XiZeroCopy =>
      ‖xiMassPolyAnalyticTest (xiMassJetPoly a N) a τ (xiSpectralPoint q)‖) := by
    have h := summable_norm_xiMassJetAnalyticTest_spectralPoint ha N hτ
    simpa only [xiMassJetAnalyticTest_eq_poly ha N τ] using h
  have hcontour := tsum_xiMassPolyAnalyticTest_eq_normalizedBottomEulerContour
    (xiMassJetPoly a N) ha0 hhalf hca hτ hsum
  rw [← hcontour, ← tsum_xiMassJetAnalyticTest_spectralPoint_eq_traceWC ha N τ]
  exact tsum_congr fun q => xiMassJetAnalyticTest_eq_poly ha N τ (xiSpectralPoint q)

end

end RHTower
