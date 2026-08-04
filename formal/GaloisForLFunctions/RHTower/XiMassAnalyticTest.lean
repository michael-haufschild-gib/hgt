import GaloisForLFunctions.RHTower.XiMassFaithfulTransfer
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# Analytic Xi mass test on its maximal branch strip

The abstract mass trace uses a pointwise principal square root after folding the centered Xi
divisor into the right half-plane.  This module identifies that term with one even holomorphic
test on the full centered divisor:

`z ↦ exp (-τ * sqrt (z² + a²))`.

The exact domain is the branch strip `|Im z| < a`.  For `a > 1/2` it contains the complete Xi
divisor, whose centered imaginary coordinates lie in `(-1/2,1/2)`.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Polynomial argument of the principal mass root. -/
def xiMassAnalyticArg (a : ℝ) (z : ℂ) : ℂ := z ^ 2 + ((a ^ 2 : ℝ) : ℂ)

theorem xiMassAnalyticArg_re (a : ℝ) (z : ℂ) :
    (xiMassAnalyticArg a z).re = z.re ^ 2 - z.im ^ 2 + a ^ 2 := by
  rw [xiMassAnalyticArg, Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re]
  ring

theorem xiMassAnalyticArg_im (a : ℝ) (z : ℂ) :
    (xiMassAnalyticArg a z).im = 2 * (z.re * z.im) := by
  rw [xiMassAnalyticArg, Complex.add_im, Complex.ofReal_im, pow_two, Complex.mul_im]
  ring

/-- Maximal horizontal strip on which the mass polynomial avoids the principal square-root cut. -/
def xiMassStrip (a : ℝ) : Set ℂ := {z | |z.im| < a}

theorem isOpen_xiMassStrip (a : ℝ) : IsOpen (xiMassStrip a) := by
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem xiMassAnalyticArg_mem_slitPlane {a : ℝ} (ha : 0 < a)
    {z : ℂ} (hz : z ∈ xiMassStrip a) :
    xiMassAnalyticArg a z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (xiMassAnalyticArg a z).im = 0
  · left
    have hzabs : |z.im| < a := hz
    have hy2 : z.im ^ 2 < a ^ 2 := by
      nlinarith [sq_abs z.im, abs_nonneg z.im]
    have hxy : z.re * z.im = 0 := by
      rw [xiMassAnalyticArg_im] at him
      nlinarith
    rcases mul_eq_zero.mp hxy with hx | hy
    · rw [xiMassAnalyticArg_re, hx]
      simp only [zero_pow, OfNat.ofNat_ne_zero, sub_eq_add_neg]
      nlinarith
    · rw [xiMassAnalyticArg_re, hy]
      simp only [zero_pow, OfNat.ofNat_ne_zero, sub_zero]
      nlinarith [sq_nonneg z.re]
  · exact Or.inr him

/-- Principal analytic mass root. -/
def xiMassAnalyticSqrt (a : ℝ) (z : ℂ) : ℂ := Complex.sqrt (xiMassAnalyticArg a z)

theorem xiMassAnalyticSqrt_sq (a : ℝ) (z : ℂ) :
    xiMassAnalyticSqrt a z ^ 2 = xiMassAnalyticArg a z := by
  simpa only [xiMassAnalyticSqrt, Complex.sqrt] using
    (Complex.cpow_nat_inv_pow (xiMassAnalyticArg a z) (by norm_num : (2 : ℕ) ≠ 0))

theorem differentiableOn_xiMassAnalyticSqrt {a : ℝ} (ha : 0 < a) :
    DifferentiableOn ℂ (xiMassAnalyticSqrt a) (xiMassStrip a) := by
  intro z hz
  exact (Complex.differentiableAt_sqrt (xiMassAnalyticArg_mem_slitPlane ha hz)).comp z
    (((differentiableAt_id.pow 2).add (differentiableAt_const ((a ^ 2 : ℝ) : ℂ)))) |>.differentiableWithinAt

theorem analyticOnNhd_xiMassAnalyticSqrt {a : ℝ} (ha : 0 < a) :
    AnalyticOnNhd ℂ (xiMassAnalyticSqrt a) (xiMassStrip a) :=
  (differentiableOn_xiMassAnalyticSqrt ha).analyticOnNhd (isOpen_xiMassStrip a)

theorem xiMassAnalyticSqrt_neg (a : ℝ) (z : ℂ) :
    xiMassAnalyticSqrt a (-z) = xiMassAnalyticSqrt a z := by
  congr 1
  simp [xiMassAnalyticArg]

/-- Even holomorphic mass test used by the Xi explicit formula. -/
def xiMassAnalyticTest (a : ℝ) (τ : ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-τ * xiMassAnalyticSqrt a z)

theorem analyticOnNhd_xiMassAnalyticTest {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    AnalyticOnNhd ℂ (xiMassAnalyticTest a τ) (xiMassStrip a) := by
  exact fun z hz => ((analyticAt_const.neg.mul
    (analyticOnNhd_xiMassAnalyticSqrt ha z hz)).cexp)

theorem xiMassAnalyticTest_neg (a : ℝ) (τ z : ℂ) :
    xiMassAnalyticTest a τ (-z) = xiMassAnalyticTest a τ z := by
  rw [xiMassAnalyticTest, xiMassAnalyticTest, xiMassAnalyticSqrt_neg]

private theorem Complex.sqrt_re_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero]
  apply Real.sqrt_pos.2
  nlinarith [Complex.re_le_norm z]

private theorem eq_of_sq_eq_sq_of_re_pos {z w : ℂ}
    (hsq : z ^ 2 = w ^ 2) (hz : 0 < z.re) (hw : 0 < w.re) : z = w := by
  have hprod : (z - w) * (z + w) = 0 := by
    calc
      (z - w) * (z + w) = z ^ 2 - w ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hre
    linarith

theorem xiMassAnalyticSqrt_spectralPoint_eq {a : ℝ} (ha : 1 / 2 ≤ a)
    (q : XiZeroCopy) :
    xiMassAnalyticSqrt a (xiSpectralPoint q) = (xiMassFamily ha).pt q := by
  have harg : xiMassAnalyticArg a (xiSpectralPoint q) = xiMassArg a q := by
    rw [xiMassAnalyticArg, xiMassArg, xiPoissonPoint_sq]
  have hargpos : 0 < (xiMassAnalyticArg a (xiSpectralPoint q)).re := by
    rw [harg]
    exact xiMassArg_re_pos ha q
  apply eq_of_sq_eq_sq_of_re_pos
  · rw [xiMassAnalyticSqrt_sq]
    change xiMassAnalyticArg a (xiSpectralPoint q) = HTGeometry.csqrt (xiMassArg a q) ^ 2
    rw [harg, HTGeometry.csqrt_sq (xiMassArg_re_pos ha q)]
  · exact Complex.sqrt_re_pos_of_re_pos hargpos
  · change 0 < HTGeometry.csqrtRe (xiMassArg a q)
    exact HTGeometry.csqrtRe_pos (xiMassArg_re_pos ha q)

theorem xiMassAnalyticTest_spectralPoint_eq {a : ℝ} (ha : 1 / 2 ≤ a)
    (τ : ℂ) (q : XiZeroCopy) :
    xiMassAnalyticTest a τ (xiSpectralPoint q) = (xiMassFamily ha).term τ q := by
  rw [xiMassAnalyticTest, HTGeometry.AbstractSpectralFamily.term,
    xiMassAnalyticSqrt_spectralPoint_eq ha]

theorem summable_norm_xiMassAnalyticTest_spectralPoint {a : ℝ} (ha : 1 / 2 ≤ a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun q : XiZeroCopy => ‖xiMassAnalyticTest a τ (xiSpectralPoint q)‖) := by
  simpa only [xiMassAnalyticTest_spectralPoint_eq ha τ] using
    (xiMassFamily ha).summable_norm_term hτ

theorem tsum_xiMassAnalyticTest_spectralPoint_eq_traceC {a : ℝ} (ha : 1 / 2 ≤ a)
    (τ : ℂ) :
    (∑' q : XiZeroCopy, xiMassAnalyticTest a τ (xiSpectralPoint q)) =
      (xiMassFamily ha).traceC τ := by
  unfold HTGeometry.AbstractSpectralFamily.traceC
  exact tsum_congr (xiMassAnalyticTest_spectralPoint_eq ha τ)

end

end RHTower
