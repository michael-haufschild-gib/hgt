import GaloisForLFunctions.RHTower.KuznetsovSpecWeightSech
import GaloisForLFunctions.RHTower.KuznetsovBesselTestFunctionWeight
import GaloisForLFunctions.HTGeometry.BesselTestFunctionTailBound
import GaloisForLFunctions.HTGeometry.ContactOrderEulerIntegral

/-!
# Bounds for the spectral weights of a test function

For a test function `φ` with `φ̃(1) = 0` and profile `G_φ`, the quotient `Q = G_φ/cosh` is

`Q(w) = S(cosh w)/4 − P(e^{−w})/2`   (`besselProfile_div_cosh`),

so with `A = ‖φ‖₁`, `B = ‖(φ/y)'‖₁`, `C = Σ_{k≥1} |φ̃(2k+1)|` and `w ≥ 0`:

* `|Q(w)| ≤ A cosh w/4 + C e^{−3w}/2`  (`norm_profileQ_le_small`),
* `|Q(w)| ≤ B/(4 cosh w) + C e^{−3w}/2`  (`norm_profileQ_le_mid`),
* `|Q(w)| ≤ B/(4 cosh w) + B/(4 sinh w)`  (`w > 0`, `norm_profileQ_le_large`).

The same-sign spectral weight at a real parameter `0 ≤ ν < ½` (exceptional or bottom of the
tempered spectrum) and at `ν = iκ` is controlled by these through
`|∫ h |W(1+it,ν)|²| ≤ 2π ∫_0^∞ |Q(w)| w cosh(2νw) dw`  (`norm_specWeight_besselWeight_real_le`) and
`|∫ h |W(1+it,iκ)|²| ≤ 4 ∫_0^∞ |Q(w)| w dw`  (`norm_specWeight_besselWeight_imag_le`).
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.DeckPointPair

noncomputable section

variable (T : BesselTestFunction)

/-- `Q = G_φ / cosh`. -/
def profileQ (w : ℝ) : ℂ := besselProfile T w / (Real.cosh w : ℂ)

theorem besselProfile_div_cosh (h1 : T.besselCoeff 1 = 0) (w : ℝ) :
    profileQ T w = T.sineTransform (Real.cosh w) / 4 - T.oddSeries (Real.exp (-w)) / 2 := by
  have hc : (Real.cosh w : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos w).ne'
  rw [profileQ, besselProfile, Pi.sub_apply, mainProfile, tailProfile_eq T h1]
  field_simp

theorem summable_norm_besselCoeff_tail :
    Summable fun k : ℕ => ‖T.besselCoeff (2 * (k + 1) + 1)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => T.norm_besselCoeff_le _) ?_
  have := (T.summable_besselMajor_mul_pow 1).comp_injective Nat.succ_injective
  simp only [one_pow, mul_one] at this
  exact this.mul_right _

/-- `|P(x)| ≤ x³ Σ_{k≥1} |φ̃(2k+1)|` for `0 ≤ x ≤ 1` when `φ̃(1) = 0`. -/
theorem norm_oddSeries_le_cube (h1 : T.besselCoeff 1 = 0) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖T.oddSeries x‖ ≤ x ^ 3 * ∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖ := by
  rw [oddSeries_eq_tail T h1, ← tsum_mul_left]
  have hb : ∀ k : ℕ, ‖besselOddCoeff T (k + 1) * ((x ^ (2 * (k + 1) + 1) : ℝ) : ℂ)‖ ≤
      x ^ 3 * ‖T.besselCoeff (2 * (k + 1) + 1)‖ := fun k => by
    rw [norm_mul, besselOddCoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_comm (x ^ 3)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (by omega)) (norm_nonneg _)
  exact tsum_of_norm_bounded ((summable_norm_besselCoeff_tail T).mul_left _).hasSum hb

/-- **Small-scale bound** `|Q(w)| ≤ A cosh w/4 + C e^{−3w}/2`, `w ≥ 0`. -/
theorem norm_profileQ_le_small (h1 : T.besselCoeff 1 = 0) {w : ℝ} (hw : 0 ≤ w) :
    ‖profileQ T w‖ ≤ Real.cosh w * (∫ y, ‖T.φ y‖) / 4 +
      Real.exp (-(3 * w)) * (∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖) / 2 := by
  rw [besselProfile_div_cosh T h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  have hS := T.norm_sineTransform_le_mul (Real.cosh w)
  rw [abs_of_pos (Real.cosh_pos w)] at hS
  have hP := norm_oddSeries_le_cube T h1 (Real.exp_pos (-w)).le
    (Real.exp_le_one_iff.2 (by linarith))
  rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * -w = -(3 * w) by push_cast; ring] at hP
  gcongr

/-- **Intermediate bound** `|Q(w)| ≤ B/(4 cosh w) + C e^{−3w}/2`, `w ≥ 0`. -/
theorem norm_profileQ_le_mid (h1 : T.besselCoeff 1 = 0) {w : ℝ} (hw : 0 ≤ w) :
    ‖profileQ T w‖ ≤ (∫ y, ‖deriv T.ψ y‖) / (4 * Real.cosh w) +
      Real.exp (-(3 * w)) * (∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖) / 2 := by
  rw [besselProfile_div_cosh T h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  have hS := T.norm_sineTransform_le_div (Real.cosh_pos w).ne'
  rw [abs_of_pos (Real.cosh_pos w)] at hS
  have hP := norm_oddSeries_le_cube T h1 (Real.exp_pos (-w)).le
    (Real.exp_le_one_iff.2 (by linarith))
  rw [← Real.exp_nat_mul, show ((3 : ℕ) : ℝ) * -w = -(3 * w) by push_cast; ring] at hP
  calc ‖T.sineTransform (Real.cosh w)‖ / 4 + ‖T.oddSeries (Real.exp (-w))‖ / 2
      ≤ (∫ y, ‖deriv T.ψ y‖) / Real.cosh w / 4 +
        Real.exp (-(3 * w)) * (∑' k : ℕ, ‖T.besselCoeff (2 * (k + 1) + 1)‖) / 2 := by gcongr
    _ = _ := by rw [div_div, mul_comm (Real.cosh w)]

/-- **Large-scale bound** `|Q(w)| ≤ B/(4 cosh w) + B/(4 sinh w)`, `w > 0`. -/
theorem norm_profileQ_le_large (h1 : T.besselCoeff 1 = 0) {w : ℝ} (hw : 0 < w) :
    ‖profileQ T w‖ ≤ (∫ y, ‖deriv T.ψ y‖) / (4 * Real.cosh w) +
      (∫ y, ‖deriv T.ψ y‖) / (4 * Real.sinh w) := by
  rw [besselProfile_div_cosh T h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, Complex.norm_ofNat, Complex.norm_ofNat]
  have hS := T.norm_sineTransform_le_div (Real.cosh_pos w).ne'
  rw [abs_of_pos (Real.cosh_pos w)] at hS
  have hP := T.norm_oddSeries_exp_neg_le hw
  calc ‖T.sineTransform (Real.cosh w)‖ / 4 + ‖T.oddSeries (Real.exp (-w))‖ / 2
      ≤ (∫ y, ‖deriv T.ψ y‖) / Real.cosh w / 4 +
        (∫ y, ‖deriv T.ψ y‖) / (2 * Real.sinh w) / 2 := by gcongr
    _ = _ := by rw [div_div, div_div, mul_comm (Real.cosh w)]; ring

theorem norm_besselProfile_eq (w : ℝ) :
    ‖besselProfile T w‖ = ‖profileQ T w‖ * Real.cosh w := by
  rw [profileQ, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.cosh_pos w).le,
    div_mul_cancel₀ _ (Real.cosh_pos w).ne']

/-- **The real-parameter weights on the half line**: for `0 ≤ ν < ½`,
`|∫ h |W(1+it, ν)|²| ≤ 2π ∫_0^∞ |Q(w)| w cosh(2νw) dw`. -/
theorem norm_specWeight_besselWeight_real_le (h1 : T.besselCoeff 1 = 0) {ν : ℝ} (h0 : 0 ≤ ν)
    (hν : ν < 1 / 2) :
    ‖specWeight (besselWeight T h1) 1 ν‖ ≤
      2 * Real.pi * ∫ w in Ioi (0 : ℝ), ‖profileQ T w‖ * (w * Real.cosh (2 * ν * w)) := by
  have h := norm_specWeight_real_le (besselOddProfile T h1) h0 hν
  have hint := integrable_norm_G_mul_abs_cosh (besselOddProfile T h1) (ν := ν)
    (by rw [abs_of_nonneg h0]; linarith)
  have he : ∀ w : ℝ, ‖(besselOddProfile T h1).G (-w)‖ * (|-w| * Real.cosh (2 * ν * -w) / Real.cosh (-w)) =
      ‖(besselOddProfile T h1).G w‖ * (|w| * Real.cosh (2 * ν * w) / Real.cosh w) := fun w => by
    rw [(besselOddProfile T h1).odd, norm_neg, abs_neg, Real.cosh_neg,
      show 2 * ν * -w = -(2 * ν * w) by ring, Real.cosh_neg]
  rw [HTGeometry.integral_even_eq_two_mul hint he] at h
  refine h.trans (le_of_eq ?_)
  rw [← mul_assoc, mul_comm Real.pi 2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : (0 : ℝ) < w := hw
  show ‖besselProfile T w‖ * _ = _
  rw [norm_besselProfile_eq, abs_of_pos hw0]
  field_simp

/-- **The tempered weights on the half line**: `|∫ h |W(1+it, iκ)|²| ≤ 4 ∫_0^∞ |Q(w)| w dw`. -/
theorem norm_specWeight_besselWeight_imag_le (h1 : T.besselCoeff 1 = 0) (κ : ℝ) :
    ‖specWeight (besselWeight T h1) 1 ((κ : ℂ) * Complex.I)‖ ≤
      4 * ∫ w in Ioi (0 : ℝ), ‖profileQ T w‖ * w := by
  have h := norm_specWeight_imag_le (besselOddProfile T h1) κ
  have hint := integrable_norm_G_mul_abs_cosh (besselOddProfile T h1) (ν := 0) (by norm_num)
  have he : ∀ w : ℝ, ‖(besselOddProfile T h1).G (-w)‖ * (|-w| * Real.cosh (2 * 0 * -w) / Real.cosh (-w)) =
      ‖(besselOddProfile T h1).G w‖ * (|w| * Real.cosh (2 * 0 * w) / Real.cosh w) := fun w => by
    rw [(besselOddProfile T h1).odd, norm_neg, abs_neg, Real.cosh_neg]
    simp
  rw [HTGeometry.integral_even_eq_two_mul hint he] at h
  refine h.trans (le_of_eq ?_)
  rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  have hw0 : (0 : ℝ) < w := hw
  show ‖besselProfile T w‖ * _ = _
  rw [norm_besselProfile_eq, abs_of_pos hw0, mul_zero, zero_mul, Real.cosh_zero, mul_one]
  field_simp

end

end GaloisForLFunctions.RHTower.DeckPointPair
