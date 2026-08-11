import GaloisForLFunctions.RHTower.XiMassAdaptiveApertureSharpFaithfulnessWall
import GaloisForLFunctions.RHTower.XiGaussianHeatTraceDisproof

/-!
# Parabolic mass-to-heat transfer on the full Xi divisor

Rest-energy renormalization turns the relativistic mass multiplier into the Gaussian heat
multiplier.  This file proves that statement on every multiplicity copy of the Xi divisor and then
passes the limit through the complete `tsum` unconditionally.

The decisive uniform estimate is not a formal pointwise Taylor expansion.  If `R + iJ` is the
Poisson coordinate and `M + iK` its mass image, then the exact square-root equation, contraction of
the imaginary coordinate, and `M ≤ a + R` imply

`a (M-a) ≥ R/4` for `a ≥ 1`.

Thus the renormalized mass term is dominated by the summable Poisson weight at heat time `t/2`,
uniformly in the aperture.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Renormalized relativistic exponent on one Xi divisor copy. -/
def xiMassParabolicExponent (a : ℝ) (q : XiZeroCopy) : ℂ :=
  (((2 * a : ℝ) : ℂ)) *
    (xiMassAnalyticSqrt a (xiSpectralPoint q) - (a : ℂ))

/-- One rest-energy-renormalized mass multiplier. -/
def xiMassParabolicTerm (a t : ℝ) (q : XiZeroCopy) : ℂ :=
  Complex.exp (-(t : ℂ) * xiMassParabolicExponent a q)

/-- The complete multiplicity-exact parabolic mass trace. -/
def xiMassParabolicTrace (a t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, xiMassParabolicTerm a t q

/-- Exact identification with the original analytic mass test after rest-energy renormalization. -/
theorem xiMassParabolicTerm_eq_restEnergyRenormalized (a t : ℝ) (q : XiZeroCopy) :
    xiMassParabolicTerm a t q =
      Complex.exp (((2 * a ^ 2 * t : ℝ) : ℂ)) *
        xiMassAnalyticTest a (((2 * a * t : ℝ) : ℂ)) (xiSpectralPoint q) := by
  rw [xiMassParabolicTerm, xiMassParabolicExponent, xiMassAnalyticTest,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact rational remainder behind the parabolic mass face. -/
theorem xiMassParabolicExponent_eq_sq_sub_remainder
    {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    xiMassParabolicExponent a q =
      xiSpectralPoint q ^ 2 -
        xiSpectralPoint q ^ 4 /
          (xiMassAnalyticSqrt a (xiSpectralPoint q) + (a : ℂ)) ^ 2 := by
  let beta : ℂ := xiMassAnalyticSqrt a (xiSpectralPoint q)
  let z : ℂ := xiSpectralPoint q
  have haPos : 0 < a := by linarith
  have hbeta : beta = (xiMassFamily ha).pt q := by
    exact xiMassAnalyticSqrt_spectralPoint_eq ha q
  have hbase : a ≤ beta.re := by
    rw [hbeta]
    exact (xiMassFamily ha).base_le q
  have hden : beta + (a : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith
  have hsq : beta ^ 2 = z ^ 2 + ((a ^ 2 : ℝ) : ℂ) := by
    dsimp only [beta, z]
    rw [xiMassAnalyticSqrt_sq, xiMassAnalyticArg]
  have hprod : (beta - (a : ℂ)) * (beta + (a : ℂ)) = z ^ 2 := by
    calc
      (beta - (a : ℂ)) * (beta + (a : ℂ)) = beta ^ 2 - ((a : ℂ) ^ 2) := by ring
      _ = z ^ 2 := by rw [hsq]; push_cast; ring
  have hdiv : beta - (a : ℂ) = z ^ 2 / (beta + (a : ℂ)) :=
    (eq_div_iff hden).2 hprod
  change (((2 * a : ℝ) : ℂ)) * (beta - (a : ℂ)) =
    z ^ 2 - z ^ 4 / (beta + (a : ℂ)) ^ 2
  calc
    (((2 * a : ℝ) : ℂ)) * (beta - (a : ℂ))
        = z ^ 2 - (beta - (a : ℂ)) ^ 2 := by
            rw [← hprod]
            push_cast
            ring
    _ = z ^ 2 - z ^ 4 / (beta + (a : ℂ)) ^ 2 := by
      rw [hdiv]
      field_simp [hden]

/-- Quantitative `O(a⁻²)` exponent error, valid on every Xi divisor copy. -/
theorem norm_xiMassParabolicExponent_sub_sq_le
    {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    ‖xiMassParabolicExponent a q - xiSpectralPoint q ^ 2‖ ≤
      ‖xiSpectralPoint q‖ ^ 4 / a ^ 2 := by
  let beta : ℂ := xiMassAnalyticSqrt a (xiSpectralPoint q)
  let z : ℂ := xiSpectralPoint q
  have haPos : 0 < a := by linarith
  have hbeta : beta = (xiMassFamily ha).pt q := by
    exact xiMassAnalyticSqrt_spectralPoint_eq ha q
  have hbase : a ≤ beta.re := by
    rw [hbeta]
    exact (xiMassFamily ha).base_le q
  have hdenNorm : a ≤ ‖beta + (a : ℂ)‖ := by
    calc
      a ≤ (beta + (a : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
      _ ≤ ‖beta + (a : ℂ)‖ := Complex.re_le_norm _
  have hdenSq : a ^ 2 ≤ ‖beta + (a : ℂ)‖ ^ 2 := by
    nlinarith [norm_nonneg (beta + (a : ℂ))]
  have herr : xiMassParabolicExponent a q - z ^ 2 =
      -(z ^ 4 / (beta + (a : ℂ)) ^ 2) := by
    dsimp only [z, beta]
    rw [xiMassParabolicExponent_eq_sq_sub_remainder ha q]
    ring
  rw [show xiSpectralPoint q = z from rfl, herr, norm_neg, norm_div, norm_pow, norm_pow]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos haPos) hdenSq

/-- The renormalized relativistic exponent converges to the Gaussian exponent on each divisor
copy, with no RH assumption. -/
theorem tendsto_xiMassParabolicExponent_atTop (q : XiZeroCopy) :
    Tendsto (fun a : ℝ => xiMassParabolicExponent a q) atTop
      (nhds (xiSpectralPoint q ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrpow : (fun a : ℝ => a ^ (2 : ℝ)) =ᶠ[atTop] fun a => a ^ (2 : ℕ) :=
    Filter.Eventually.of_forall fun a => Real.rpow_natCast a 2
  have hpowTop : Tendsto (fun a : ℝ => a ^ (2 : ℕ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).congr' hrpow
  have hmajor : Tendsto (fun a : ℝ => ‖xiSpectralPoint q‖ ^ 4 / a ^ 2)
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hpowTop
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 / 2 : ℝ)] with a ha
  exact norm_xiMassParabolicExponent_sub_sq_le ha q

/-- Pointwise parabolic mass-to-Gaussian convergence. -/
theorem tendsto_xiMassParabolicTerm_atTop (t : ℝ) (q : XiZeroCopy) :
    Tendsto (fun a : ℝ => xiMassParabolicTerm a t q) atTop
      (nhds (xiGaussianHeatTerm t q)) := by
  have hinner : Tendsto
      (fun a : ℝ => -(t : ℂ) * xiMassParabolicExponent a q) atTop
      (nhds (-(t : ℂ) * xiSpectralPoint q ^ 2)) :=
    tendsto_const_nhds.mul (tendsto_xiMassParabolicExponent_atTop q)
  simpa only [xiMassParabolicTerm, xiGaussianHeatTerm, Function.comp_def] using
    Complex.continuous_exp.continuousAt.tendsto.comp hinner

/-- Uniform raised-height gap.  This is the estimate that makes the full-divisor limit possible. -/
theorem xiMassParabolic_heightGap_lower
    {a : ℝ} (ha : 1 ≤ a) (q : XiZeroCopy) :
    (xiPoissonPoint q).re / 4 ≤
      a * ((xiMassAnalyticSqrt a (xiSpectralPoint q)).re - a) := by
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let beta : ℂ := xiMassAnalyticSqrt a (xiSpectralPoint q)
  let M : ℝ := beta.re
  let K : ℝ := beta.im
  have haHalf : 1 / 2 ≤ a := by linarith
  have hbeta : beta = (xiMassFamily haHalf).pt q := by
    exact xiMassAnalyticSqrt_spectralPoint_eq haHalf q
  have hR : 3 < R := by simpa only [R] using three_lt_xiPoissonPoint_re q
  have hJsq : J ^ 2 < 1 / 4 := by
    have hJ : |J| < 1 / 2 := by
      simpa only [J] using abs_xiPoissonPoint_im_lt_half q
    nlinarith [sq_abs J, abs_nonneg J]
  have hMge : a ≤ M := by
    dsimp only [M]
    rw [hbeta]
    exact (xiMassFamily haHalf).base_le q
  have hMupper : M ≤ a + R := by
    dsimp only [M, R]
    rw [hbeta]
    exact xiMassFamily_height_le_aperture_add_original haHalf q
  have hsq : beta ^ 2 = xiPoissonPoint q ^ 2 + ((a ^ 2 : ℝ) : ℂ) := by
    dsimp only [beta]
    rw [xiMassAnalyticSqrt_sq, xiMassAnalyticArg, xiPoissonPoint_sq]
  have hre := congrArg Complex.re hsq
  have hreal : M ^ 2 - K ^ 2 = R ^ 2 - J ^ 2 + a ^ 2 := by
    dsimp only [M, K, R, J]
    simpa only [pow_two, Complex.mul_re, Complex.add_re, Complex.ofReal_re] using hre
  have hprod : (M - a) * (M + a) = R ^ 2 - J ^ 2 + K ^ 2 := by
    nlinarith
  have hprodLower : R ^ 2 - 1 / 4 < (M - a) * (M + a) := by
    rw [hprod]
    nlinarith [sq_nonneg K]
  have hdelta : 0 ≤ M - a := sub_nonneg.mpr hMge
  by_cases hRa : R ≤ a
  · have hden : M + a ≤ 3 * a := by linarith
    have hprodUpper : (M - a) * (M + a) ≤ (M - a) * (3 * a) :=
      mul_le_mul_of_nonneg_left hden hdelta
    change R / 4 ≤ a * (M - a)
    nlinarith
  · have haR : a < R := lt_of_not_ge hRa
    have hden : M + a < 3 * R := by linarith
    have hprodUpper : (M - a) * (M + a) ≤ (M - a) * (3 * R) :=
      mul_le_mul_of_nonneg_left hden.le hdelta
    have hgap : R / 4 < M - a := by nlinarith
    have hscale : M - a ≤ a * (M - a) := by
      calc
        M - a = 1 * (M - a) := by ring
        _ ≤ a * (M - a) := mul_le_mul_of_nonneg_right ha hdelta
    change R / 4 ≤ a * (M - a)
    exact hgap.le.trans hscale

/-- Uniform summable majorant for every positive heat time and every aperture `a ≥ 1`. -/
theorem norm_xiMassParabolicTerm_le_poissonWeight
    {a t : ℝ} (ha : 1 ≤ a) (ht : 0 < t) (q : XiZeroCopy) :
    ‖xiMassParabolicTerm a t q‖ ≤ xiPoissonWeight (t / 2) q := by
  have haHalf : 1 / 2 ≤ a := by linarith
  have hroot : xiMassAnalyticSqrt a (xiSpectralPoint q) = (xiMassFamily haHalf).pt q :=
    xiMassAnalyticSqrt_spectralPoint_eq haHalf q
  have hgap := xiMassParabolic_heightGap_lower ha q
  rw [hroot] at hgap
  have hscaled := mul_le_mul_of_nonneg_left hgap ht.le
  rw [xiMassParabolicTerm, Complex.norm_exp, xiPoissonWeight]
  apply Real.exp_le_exp.mpr
  rw [xiMassParabolicExponent, hroot]
  simp only [Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul]
  nlinarith [hscaled]

/-- **Full-divisor parabolic transfer.**  Rest-energy-renormalized Xi mass traces converge to the
Gaussian Xi heat trace at every positive time, unconditionally and with exact multiplicities. -/
theorem tendsto_xiMassParabolicTrace_atTop {t : ℝ} (ht : 0 < t) :
    Tendsto (fun a : ℝ => xiMassParabolicTrace a t) atTop
      (nhds (xiGaussianHeatTrace t)) := by
  change Tendsto (fun a : ℝ => ∑' q : XiZeroCopy, xiMassParabolicTerm a t q) atTop
    (nhds (∑' q : XiZeroCopy, xiGaussianHeatTerm t q))
  apply tendsto_tsum_of_dominated_convergence (summable_xiPoissonWeight (by linarith : 0 < t / 2))
  · exact fun q => tendsto_xiMassParabolicTerm_atTop t q
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact fun q => norm_xiMassParabolicTerm_le_poissonWeight ha ht q

end

end RHTower
