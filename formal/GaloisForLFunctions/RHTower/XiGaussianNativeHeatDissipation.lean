import GaloisForLFunctions.RHTower.XiGaussianUniformHeatHalfLine
import GaloisForLFunctions.RHTower.XiEndpointStrongHeightGap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Curvature-controlled native heat dissipation, uniformly in polynomial order

The endpoint-source height gap and the open critical strip put every actual
squared spectral node in the sector `81 * norm w < 83 * re w`. Consequently
`83 K + 81 sigma H` decreases with heat time for every real `|sigma| <= 1`.
The trace here is the complete polynomial-square trace. No coefficient cross
term or divisor multiplicity is discarded, and the constant is independent
of degree, coefficients, and the positive heat times being compared.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower

/-- The sharpened completed-curvature height gap yields a narrow sector for
every squared spectral node, without identifying any zero numerically. -/
theorem xiSpectralSq_native_heat_sector (q : XiZeroCopy) :
    81 * ‖xiSpectralPoint q ^ 2‖ < 83 * (xiSpectralPoint q ^ 2).re := by
  have hheight := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hwidth := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  have him : (xiSpectralPoint q).im = -((q.1 : ℂ).re - 1 / 2) := by
    simp [xiSpectralPoint]
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re, hre, him]
  nlinarith only [hheight, hwidth]

private theorem scalar_corrected_heat_antitone (z w : ℂ)
    (hw : 81 * ‖w‖ ≤ 83 * w.re) (σ : Set.Icc (-1 : ℝ) 1) :
    Antitone (fun t : ℝ =>
      83 * ‖z‖ ^ 2 * Real.exp (-t * w.re) +
        81 * (σ : ℝ) * (z ^ 2 * Complex.exp (-(t : ℂ) * w)).re) := by
  have hderiv (t : ℝ) : HasDerivAt
      (fun s : ℝ => 83 * ‖z‖ ^ 2 * Real.exp (-s * w.re) +
        81 * (σ : ℝ) * (z ^ 2 * Complex.exp (-(s : ℂ) * w)).re)
      (83 * ‖z‖ ^ 2 * (Real.exp (-t * w.re) * -w.re) +
        81 * (σ : ℝ) * (z ^ 2 * (Complex.exp (-(t : ℂ) * w) * -w)).re) t := by
    have hR := (((hasDerivAt_id t).neg.mul_const w.re).exp).const_mul (83 * ‖z‖ ^ 2)
    have hC := ((((hasDerivAt_id (t : ℂ)).neg.mul_const w).cexp).const_mul
      (z ^ 2)).real_of_complex.const_mul (81 * (σ : ℝ))
    convert! hR.add hC using 1
    simp only [Pi.neg_apply, id_eq, neg_mul, one_mul]
  apply antitone_of_hasDerivAt_nonpos hderiv
  intro t
  have hσ : |(σ : ℝ)| ≤ 1 := abs_le.mpr σ.property
  let v := z ^ 2 * (Complex.exp (-(t : ℂ) * w) * -w)
  have hv : (σ : ℝ) * v.re ≤ ‖w‖ * ‖z‖ ^ 2 * Real.exp (-t * w.re) := by
    calc
      _ ≤ |(σ : ℝ) * v.re| := le_abs_self _
      _ = |(σ : ℝ)| * |v.re| := abs_mul _ _
      _ ≤ 1 * ‖v‖ := mul_le_mul hσ (Complex.abs_re_le_norm v)
        (abs_nonneg _) zero_le_one
      _ = _ := by
        simp only [v, norm_mul, norm_pow, norm_neg, Complex.norm_exp,
          Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
          Complex.ofReal_im, neg_zero, zero_mul, sub_zero, one_mul]
        ring
  have hscaled := mul_le_mul_of_nonneg_right hw
    (mul_nonneg (sq_nonneg ‖z‖) (Real.exp_pos (-t * w.re)).le)
  change 83 * ‖z‖ ^ 2 * (Real.exp (-t * w.re) * -w.re) +
    81 * (σ : ℝ) * v.re ≤ 0
  nlinarith only [hv, hscaled]

/-- Full signed trace corrected by native energy decreases with time.
One pair of constants works for every polynomial, hence every Hankel order. -/
theorem xiGaussianNative_corrected_trace_antitone (P : Polynomial ℝ)
    (σ : Set.Icc (-1 : ℝ) 1) :
    Antitone (fun t : {t : ℝ // 0 < t} =>
      83 * xiGaussianNativeEnergy P t +
        81 * (σ : ℝ) * xiPolynomialGaussianHeatTraceReal P t) := by
  have hs (t : {t : ℝ // 0 < t}) := summable_xiPolynomialGaussianHeatTerm t.property P
  have hsum (t : {t : ℝ // 0 < t}) :
      83 * xiGaussianNativeEnergy P t +
        81 * (σ : ℝ) * xiPolynomialGaussianHeatTraceReal P t =
      ∑' q : XiZeroCopy, (83 * ‖xiPolynomialGaussianHeatTerm P t q‖ +
        81 * (σ : ℝ) * (xiPolynomialGaussianHeatTerm P t q).re) := by
    rw [Summable.tsum_add ((hs t).norm.mul_left 83)
      (((Complex.hasSum_re (hs t).hasSum).summable).mul_left (81 * (σ : ℝ))),
      tsum_mul_left, tsum_mul_left, ← Complex.re_tsum (hs t)]
    rfl
  intro s t hst
  dsimp only
  rw [hsum, hsum]
  apply Summable.tsum_le_tsum _
    (((hs t).norm.mul_left 83).add
      (((Complex.hasSum_re (hs t).hasSum).summable).mul_left (81 * (σ : ℝ))))
    (((hs s).norm.mul_left 83).add
      (((Complex.hasSum_re (hs s).hasSum).summable).mul_left (81 * (σ : ℝ))))
  intro q
  have h := scalar_corrected_heat_antitone
    (evalRealPolynomial P (xiSpectralPoint q ^ 2)) (xiSpectralPoint q ^ 2)
    (xiSpectralSq_native_heat_sector q).le σ (show (s : ℝ) ≤ (t : ℝ) from hst)
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm]
  simpa only [xiPolynomialGaussianHeatTerm,
    xiGaussianHeatTerm, neg_mul, mul_assoc] using h

/-- Actual signed heat variation is paid for by native energy dissipated
between the same two times, with no degree-dependent loss. -/
theorem abs_xiGaussianHeatTraceReal_sub_le_native_dissipation
    (P : Polynomial ℝ) (s : {s : ℝ // 0 < s})
    (t : Set.Ici (s : ℝ)) :
    |xiPolynomialGaussianHeatTraceReal P t - xiPolynomialGaussianHeatTraceReal P s| ≤
      (83 / 81 : ℝ) * (xiGaussianNativeEnergy P s -
        xiGaussianNativeEnergy P (xiGaussianHeatAfter s t)) := by
  have hp := xiGaussianNative_corrected_trace_antitone P
    ⟨1, by constructor <;> norm_num⟩
    (show s ≤ xiGaussianHeatAfter s t from t.property)
  have hm := xiGaussianNative_corrected_trace_antitone P
    ⟨-1, by constructor <;> norm_num⟩
    (show s ≤ xiGaussianHeatAfter s t from t.property)
  change 83 * xiGaussianNativeEnergy P (xiGaussianHeatAfter s t) +
    81 * 1 * xiPolynomialGaussianHeatTraceReal P t ≤
    83 * xiGaussianNativeEnergy P s + 81 * 1 * xiPolynomialGaussianHeatTraceReal P s at hp
  change 83 * xiGaussianNativeEnergy P (xiGaussianHeatAfter s t) +
    81 * -1 * xiPolynomialGaussianHeatTraceReal P t ≤
    83 * xiGaussianNativeEnergy P s + 81 * -1 * xiPolynomialGaussianHeatTraceReal P s at hm
  rw [abs_le]
  constructor <;> linarith only [hp, hm]

end RHTower
