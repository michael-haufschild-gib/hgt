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
      nlinarith
    · rw [xiMassAnalyticArg_re, hy]
      nlinarith [sq_nonneg z.re]
  · exact Or.inr him

/-- Principal analytic mass root. -/
def xiMassAnalyticSqrt (a : ℝ) (z : ℂ) : ℂ := Complex.sqrt (xiMassAnalyticArg a z)

theorem xiMassAnalyticSqrt_sq (a : ℝ) (z : ℂ) :
    xiMassAnalyticSqrt a z ^ 2 = xiMassAnalyticArg a z := by
  unfold xiMassAnalyticSqrt Complex.sqrt
  change ((xiMassAnalyticArg a z) ^ (((2 : ℕ) : ℂ)⁻¹)) ^ 2 = xiMassAnalyticArg a z
  exact Complex.cpow_nat_inv_pow (xiMassAnalyticArg a z) (by norm_num : (2 : ℕ) ≠ 0)

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
  apply congrArg Complex.sqrt
  unfold xiMassAnalyticArg
  ring

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

/-- The mass polynomial has positive real part throughout its branch strip. -/
theorem xiMassAnalyticArg_re_pos {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ xiMassStrip a) : 0 < (xiMassAnalyticArg a z).re := by
  rw [xiMassAnalyticArg_re]
  have hy2 : z.im ^ 2 < a ^ 2 := by
    have := hz
    change |z.im| < a at this
    nlinarith [sq_abs z.im, abs_nonneg z.im]
  nlinarith [sq_nonneg z.re]

/-- Reverse-triangle lower bound for the norm of the mass polynomial. -/
theorem xiMassAnalyticArg_norm_lower (a : ℝ) (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 - a ^ 2 ≤ ‖xiMassAnalyticArg a z‖ := by
  have h := norm_sub_norm_le (z ^ 2) (-((a ^ 2 : ℝ) : ℂ))
  rw [show z ^ 2 - -((a ^ 2 : ℝ) : ℂ) = xiMassAnalyticArg a z by
    unfold xiMassAnalyticArg; ring] at h
  rw [norm_pow, Complex.sq_norm, Complex.normSq_apply] at h
  simp only [norm_neg, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg a)] at h
  nlinarith

/-- Exact real-square formula for the principal analytic mass root. -/
theorem xiMassAnalyticSqrt_re_sq (a : ℝ) (z : ℂ) :
    (xiMassAnalyticSqrt a z).re ^ 2 =
      (‖xiMassAnalyticArg a z‖ + (xiMassAnalyticArg a z).re) / 2 := by
  have hsq := xiMassAnalyticSqrt_sq a z
  have hre := congrArg Complex.re hsq
  rw [xiMassAnalyticArg_re] at hre
  simp only [pow_two, Complex.mul_re] at hre
  have hnorm := congrArg norm hsq
  rw [norm_pow] at hnorm
  have hwNorm :
      (xiMassAnalyticSqrt a z).re ^ 2 + (xiMassAnalyticSqrt a z).im ^ 2 =
        ‖xiMassAnalyticArg a z‖ := by
    simp only [pow_two]
    rw [← Complex.normSq_apply, ← Complex.sq_norm]
    exact hnorm
  rw [xiMassAnalyticArg_re]
  nlinarith

/-- The real part of the principal mass root dominates the horizontal coordinate. -/
theorem abs_re_le_xiMassAnalyticSqrt_re (a : ℝ) (z : ℂ) :
    |z.re| ≤ (xiMassAnalyticSqrt a z).re := by
  have hsq := xiMassAnalyticSqrt_re_sq a z
  have hnorm := xiMassAnalyticArg_norm_lower a z
  have harg := xiMassAnalyticArg_re a z
  have hsqrt_nonneg : 0 ≤ (xiMassAnalyticSqrt a z).re := by
    rw [xiMassAnalyticSqrt, Complex.sqrt_eq_real_add_ite]
    split_ifs <;> simp [Complex.mul_re] <;> positivity
  have hsquare : z.re ^ 2 ≤ (xiMassAnalyticSqrt a z).re ^ 2 := by
    rw [hsq, harg]
    linarith
  exact (sq_le_sq₀ (abs_nonneg z.re) hsqrt_nonneg).mp
    (by simpa [sq_abs] using hsquare)

/-- The principal mass root has strictly positive real part on the mass strip. -/
theorem xiMassAnalyticSqrt_re_pos {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ xiMassStrip a) : 0 < (xiMassAnalyticSqrt a z).re := by
  rw [xiMassAnalyticSqrt, Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp [Complex.mul_re]
  all_goals nlinarith [xiMassAnalyticArg_re_pos ha hz,
    Complex.re_le_norm (xiMassAnalyticArg a z)]

/-- The imaginary part of the mass root is no larger than the vertical coordinate. -/
theorem abs_xiMassAnalyticSqrt_im_le {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ xiMassStrip a) :
    |(xiMassAnalyticSqrt a z).im| ≤ |z.im| := by
  let w := xiMassAnalyticSqrt a z
  have hA : |z.re| ≤ w.re := abs_re_le_xiMassAnalyticSqrt_re a z
  have hApos : 0 < w.re := xiMassAnalyticSqrt_re_pos ha hz
  have him := congrArg Complex.im (xiMassAnalyticSqrt_sq a z)
  rw [xiMassAnalyticArg_im] at him
  simp only [pow_two, Complex.mul_im] at him
  have hAB : w.re * w.im = z.re * z.im := by nlinarith
  by_cases hx : z.re = 0
  · rw [hx] at hAB
    simp only [zero_mul] at hAB
    have hB : w.im = 0 := (mul_eq_zero.mp hAB).resolve_left hApos.ne'
    change |w.im| ≤ |z.im|
    simp [hB]
  · have hxabs : 0 < |z.re| := abs_pos.mpr hx
    have habs := congrArg abs hAB
    rw [abs_mul, abs_mul, abs_of_pos hApos] at habs
    have hmul : |z.re| * |w.im| ≤ |z.re| * |z.im| := by
      calc
        |z.re| * |w.im| ≤ w.re * |w.im| :=
          mul_le_mul_of_nonneg_right hA (abs_nonneg w.im)
        _ = |z.re| * |z.im| := habs
    exact le_of_mul_le_mul_left hmul hxabs

/-- Exponential strip bound for the analytic mass test. -/
theorem norm_xiMassAnalyticTest_le {a : ℝ} (ha : 0 < a) {τ z : ℂ}
    (hτ : 0 ≤ τ.re) (hz : z ∈ xiMassStrip a) :
    ‖xiMassAnalyticTest a τ z‖ ≤
      Real.exp (-τ.re * |z.re| + |τ.im| * |z.im|) := by
  rw [xiMassAnalyticTest, Complex.norm_exp, Real.exp_le_exp]
  have hA := abs_re_le_xiMassAnalyticSqrt_re a z
  have hB := abs_xiMassAnalyticSqrt_im_le ha hz
  have hreal := mul_le_mul_of_nonneg_left hA hτ
  have hcross1 : τ.im * (xiMassAnalyticSqrt a z).im ≤
      |τ.im| * |(xiMassAnalyticSqrt a z).im| := by
    rw [← abs_mul]
    exact le_abs_self _
  have hcross2 := mul_le_mul_of_nonneg_left hB (abs_nonneg τ.im)
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im]
  linarith

/-- Derivative of the mass polynomial. -/
theorem hasDerivAt_xiMassAnalyticArg (a : ℝ) (z : ℂ) :
    HasDerivAt (xiMassAnalyticArg a) (2 * z) z := by
  change HasDerivAt (fun w : ℂ => w ^ 2 + ((a ^ 2 : ℝ) : ℂ)) (2 * z) z
  simpa [id, mul_comm] using
    ((hasDerivAt_id z).pow 2).add_const ((a ^ 2 : ℝ) : ℂ)

/-- Derivative of the principal analytic mass root inside its branch strip. -/
theorem hasDerivAt_xiMassAnalyticSqrt {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z ∈ xiMassStrip a) :
    HasDerivAt (xiMassAnalyticSqrt a) (z / xiMassAnalyticSqrt a z) z := by
  have hcomp := (Complex.hasDerivAt_sqrt
    (xiMassAnalyticArg_mem_slitPlane ha hz)).comp z (hasDerivAt_xiMassAnalyticArg a z)
  change HasDerivAt (xiMassAnalyticSqrt a)
    (xiMassAnalyticArg a z ^ (-1 / 2) / 2 * (2 * z)) z at hcomp
  convert hcomp using 1
  rw [show (-1 / 2 : ℂ) = -(2⁻¹ : ℂ) by ring, Complex.cpow_neg]
  change z / xiMassAnalyticSqrt a z =
    ((xiMassAnalyticSqrt a z)⁻¹ / 2) * (2 * z)
  have hw0 : xiMassAnalyticSqrt a z ≠ 0 := by
    intro hw
    have := congrArg Complex.re hw
    simp only [Complex.zero_re] at this
    linarith [xiMassAnalyticSqrt_re_pos ha hz]
  field_simp [hw0]

/-- Derivative of the analytic mass test inside its branch strip. -/
theorem hasDerivAt_xiMassAnalyticTest {a : ℝ} (ha : 0 < a) (τ : ℂ) {z : ℂ}
    (hz : z ∈ xiMassStrip a) :
    HasDerivAt (xiMassAnalyticTest a τ)
      (-τ * (z / xiMassAnalyticSqrt a z) * xiMassAnalyticTest a τ z) z := by
  have hinner := (hasDerivAt_const z (-τ)).mul (hasDerivAt_xiMassAnalyticSqrt ha hz)
  have hcomp := (Complex.hasDerivAt_exp (-τ * xiMassAnalyticSqrt a z)).comp z hinner
  change HasDerivAt (xiMassAnalyticTest a τ)
    (Complex.exp (-τ * xiMassAnalyticSqrt a z) *
      (0 * xiMassAnalyticSqrt a z + -τ * (z / xiMassAnalyticSqrt a z))) z at hcomp
  convert hcomp using 1
  simp only [xiMassAnalyticTest]
  ring

private theorem Complex.sqrt_re_pos_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    0 < (Complex.sqrt z).re := by
  rw [Complex.sqrt_eq_real_add_ite]
  split_ifs <;> simp [Complex.mul_re]
  all_goals nlinarith [Complex.re_le_norm z]

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
