import GaloisForLFunctions.RHTower.RouteRBurnolXiPrimeTwoCompletionMultiplier
import GaloisForLFunctions.RHTower.LogModulusHorizontal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Strict normal dissipation of the prime-two Burnol--Xi completion

The coefficient-faithful completion multiplier

`C₂(w) = w² (w - 1) / (2 (2^w - 1))`

is not merely nonvanishing on the critical strip.  Its horizontal logarithmic energy slope on the
critical line has a uniform negative gap.  This is the first source orientation reversal available
after the exact Burnol-to-Xi landing: diagonal multiplication is positive on energy, but its normal
Green current is strictly dissipative.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Explicit horizontal derivative of `log ‖C₂(w)‖²` at `w = 1/2 + ix`. -/
def burnolXiCompletionCriticalNormalLogEnergySlope (x : ℝ) : ℝ :=
  1 / (x ^ 2 + 1 / 4) -
    2 * Real.log 2 *
      ((2 - Real.sqrt 2 * Real.cos (Real.log 2 * x)) /
        (3 - 2 * Real.sqrt 2 * Real.cos (Real.log 2 * x)))

/-- The elementary constants needed by the normal-current estimate. -/
private theorem burnolXiCompletion_normal_constants :
    (3 / 5 : ℝ) < Real.log 2 ∧ Real.log 2 < 7 / 10 ∧
      (7 / 5 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 10 / 7 := by
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtNonneg := Real.sqrt_nonneg 2
  constructor
  · linarith [Real.log_two_gt_d9]
  constructor
  · linarith [Real.log_two_lt_d9]
  constructor <;> nlinarith

/-- The exact dyadic denominator is positive on the critical line. -/
private theorem burnolXiCompletion_critical_denominator_pos (x : ℝ) :
    0 < 3 - 2 * Real.sqrt 2 * Real.cos (Real.log 2 * x) := by
  have hsqrt := burnolXiCompletion_normal_constants
  have hcos := Real.cos_le_one (Real.log 2 * x)
  nlinarith [Real.sqrt_nonneg 2]

private theorem one_div_add_half_eq_div (a : ℝ) (ha : a ≠ 0) :
    1 / a + 1 / 2 = (1 + a / 2) / a := by
  field_simp

set_option maxHeartbeats 800000

/-- **Uniform prime-two normal dissipation.**  The horizontal logarithmic energy current of the
exact completion multiplier has a strict half-unit inward gap at every height.  The proof is
global: `cos y ≥ 1 - y²/2` reduces the rational trigonometric expression to a quadratic with three
strictly positive coefficients. -/
theorem burnolXiCompletionCriticalNormalLogEnergySlope_lt_neg_half (x : ℝ) :
    burnolXiCompletionCriticalNormalLogEnergySlope x < -(1 / 2 : ℝ) := by
  let L : ℝ := Real.log 2
  let r : ℝ := Real.sqrt 2
  let z : ℝ := x ^ 2
  let c : ℝ := Real.cos (L * x)
  let c₀ : ℝ := 1 - L ^ 2 * z / 2
  have hconstants := burnolXiCompletion_normal_constants
  have hLlo : (3 / 5 : ℝ) < L := by simpa [L] using hconstants.1
  have hLhi : L < 7 / 10 := by simpa [L] using hconstants.2.1
  have hrlo : (7 / 5 : ℝ) < r := by simpa [r] using hconstants.2.2.1
  have hrhi : r < 10 / 7 := by simpa [r] using hconstants.2.2.2
  have hLpos : 0 < L := by linarith
  have hrpos : 0 < r := by linarith
  have hrsq : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hc_le : c ≤ 1 := by
    dsimp [c]
    exact Real.cos_le_one _
  have hc₀_le_c : c₀ ≤ c := by
    have hcos := Real.one_sub_sq_div_two_le_cos (x := L * x)
    dsimp [c₀, c, z]
    nlinarith [sq_nonneg (L * x)]
  have hden : 0 < 3 - 2 * r * c := by
    nlinarith
  have hden₀ : 0 < 3 - 2 * r * c₀ := by
    nlinarith
  have hratio :
      (2 - r * c₀) / (3 - 2 * r * c₀) ≤
        (2 - r * c) / (3 - 2 * r * c) := by
    rw [div_le_div_iff₀ hden₀ hden]
    nlinarith
  have hApos : 0 < 2 - r := by linarith
  have hBpos : 0 < 3 - 2 * r := by nlinarith
  have hnum₀ : 0 < (2 - r) + r * L ^ 2 * z / 2 := by positivity
  have hden₀' : 0 < (3 - 2 * r) + r * L ^ 2 * z := by positivity
  have hratio' :
      ((2 - r) + r * L ^ 2 * z / 2) /
          ((3 - 2 * r) + r * L ^ 2 * z) ≤
        (2 - r * c) / (3 - 2 * r * c) := by
    have hnumEq : 2 - r * c₀ = (2 - r) + r * L ^ 2 * z / 2 := by
      dsimp [c₀]
      ring
    have hdenEq : 3 - 2 * r * c₀ = (3 - 2 * r) + r * L ^ 2 * z := by
      dsimp [c₀]
      ring
    simpa [hnumEq, hdenEq] using hratio
  have hAupper : 2 - r < 3 / 5 := by linarith
  have hL69 : (69 / 100 : ℝ) < L := by
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hLA : (9 / 8 : ℝ) * (2 - r) < L := by
    calc
      (9 / 8 : ℝ) * (2 - r) < (9 / 8) * (3 / 5) := by gcongr
      _ < 69 / 100 := by norm_num
      _ < L := hL69
  have hconstant : 0 < L * (2 - r) / 2 - (9 / 8) * (3 - 2 * r) := by
    have hprod : 0 < (L - (9 / 8) * (2 - r)) * (2 - r) :=
      mul_pos (sub_pos.mpr hLA) hApos
    nlinarith
  have hA47 : (4 / 7 : ℝ) < 2 - r := by linarith
  have hmain : (138 / 175 : ℝ) < 2 * L * (2 - r) := by
    have hp₁ : (69 / 100 : ℝ) * (4 / 7) < L * (4 / 7) :=
      mul_lt_mul_of_pos_right hL69 (by norm_num)
    have hp₂ : L * (4 / 7) < L * (2 - r) :=
      mul_lt_mul_of_pos_left hA47 hLpos
    nlinarith
  have hB : 3 - 2 * r < 1 / 5 := by linarith
  have hLsq : L ^ 2 < (49 / 100 : ℝ) := by nlinarith
  have hfactor : 9 / 8 - L / 4 < (24 / 25 : ℝ) := by linarith
  have hfactorPos : 0 < 9 / 8 - L / 4 := by linarith
  have hneg : r * L ^ 2 * (9 / 8 - L / 4) < (17 / 25 : ℝ) := by
    calc
      r * L ^ 2 * (9 / 8 - L / 4) <
          (10 / 7) * L ^ 2 * (9 / 8 - L / 4) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hrhi (sq_pos_of_pos hLpos)) hfactorPos
      _ < (10 / 7) * (49 / 100) * (9 / 8 - L / 4) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left hLsq (by norm_num)) hfactorPos
      _ < (10 / 7) * (49 / 100) * (24 / 25) := by
        exact mul_lt_mul_of_pos_left hfactor (by norm_num)
      _ < 17 / 25 := by norm_num
  have hlinear :
      0 < 2 * L * (2 - r) + r * L ^ 3 / 4 -
        (3 - 2 * r) / 2 - 9 * r * L ^ 2 / 8 := by
    have hrearrange :
        r * L ^ 3 / 4 - 9 * r * L ^ 2 / 8 =
          -(r * L ^ 2 * (9 / 8 - L / 4)) := by ring
    rw [show 2 * L * (2 - r) + r * L ^ 3 / 4 -
        (3 - 2 * r) / 2 - 9 * r * L ^ 2 / 8 =
      2 * L * (2 - r) - (3 - 2 * r) / 2 -
        r * L ^ 2 * (9 / 8 - L / 4) by ring]
    nlinarith
  have hquadratic : 0 < r * L ^ 2 * (L - 1 / 2) := by
    exact mul_pos (mul_pos hrpos (sq_pos_of_pos hLpos)) (by linarith)
  have hpoly :
      (1 + (z + 1 / 4) / 2) * ((3 - 2 * r) + r * L ^ 2 * z) <
        2 * L * (z + 1 / 4) * ((2 - r) + r * L ^ 2 * z / 2) := by
    have hq := mul_nonneg hquadratic.le (sq_nonneg z)
    have hl := mul_nonneg hlinear.le hz
    nlinarith
  have hzden : 0 < z + 1 / 4 := by positivity
  have hfrac :
      1 / (z + 1 / 4) + 1 / 2 <
        2 * L *
          (((2 - r) + r * L ^ 2 * z / 2) /
            ((3 - 2 * r) + r * L ^ 2 * z)) := by
    have hquot :
        (1 + (z + 1 / 4) / 2) / (z + 1 / 4) <
          (2 * L * ((2 - r) + r * L ^ 2 * z / 2)) /
            ((3 - 2 * r) + r * L ^ 2 * z) := by
      apply (div_lt_div_iff₀ hzden hden₀').2
      calc
        (1 + (z + 1 / 4) / 2) * ((3 - 2 * r) + r * L ^ 2 * z) <
            2 * L * (z + 1 / 4) * ((2 - r) + r * L ^ 2 * z / 2) := hpoly
        _ = (2 * L * ((2 - r) + r * L ^ 2 * z / 2)) *
            (z + 1 / 4) := by ring
    calc
      1 / (z + 1 / 4) + 1 / 2 =
          (1 + (z + 1 / 4) / 2) / (z + 1 / 4) :=
        one_div_add_half_eq_div _ hzden.ne'
      _ < (2 * L * ((2 - r) + r * L ^ 2 * z / 2)) /
          ((3 - 2 * r) + r * L ^ 2 * z) := hquot
      _ = 2 * L *
          (((2 - r) + r * L ^ 2 * z / 2) /
            ((3 - 2 * r) + r * L ^ 2 * z)) := mul_div_assoc _ _ _
  have hscaled :
      2 * L *
          (((2 - r) + r * L ^ 2 * z / 2) /
            ((3 - 2 * r) + r * L ^ 2 * z)) ≤
        2 * L * ((2 - r * c) / (3 - 2 * r * c)) :=
    mul_le_mul_of_nonneg_left hratio' (by positivity)
  have hfinal :
      1 / (z + 1 / 4) + 1 / 2 <
        2 * L * ((2 - r * c) / (3 - 2 * r * c)) :=
    hfrac.trans_le hscaled
  dsimp [burnolXiCompletionCriticalNormalLogEnergySlope, L, r, z, c] at hfinal ⊢
  linarith

/-- In particular, the source completion normal current is strictly negative everywhere. -/
theorem burnolXiCompletionCriticalNormalLogEnergySlope_neg (x : ℝ) :
    burnolXiCompletionCriticalNormalLogEnergySlope x < 0 :=
  (burnolXiCompletionCriticalNormalLogEnergySlope_lt_neg_half x).trans (by norm_num)

/-! ## Identification with the analytic normal derivative -/

/-- Logarithmic derivative dictated by the Euler differential and prime-two dilation factors. -/
def burnolXiCompletionLogDerivative (w : ℂ) : ℂ :=
  2 / w + 1 / (w - 1) -
    (Real.log 2 : ℂ) * ((2 : ℂ) ^ w / ((2 : ℂ) ^ w - 1))

private theorem two_cpow_criticalLineArgument_re (x : ℝ) :
    ((2 : ℂ) ^ burnolXiCriticalLineArgument x).re =
      Real.sqrt 2 * Real.cos (Real.log 2 * x) := by
  have hsqrt : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hlogre : (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  have hlogim : (Complex.log (2 : ℂ)).im = 0 := by
    rw [Complex.log_im, Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.cpow_def_of_ne_zero (by norm_num), Complex.exp_re]
  have hre : (Complex.log (2 : ℂ) * burnolXiCriticalLineArgument x).re = Real.log 2 / 2 := by
    rw [Complex.mul_re]
    rw [hlogre, hlogim]
    simp [burnolXiCriticalLineArgument]
    ring
  have him : (Complex.log (2 : ℂ) * burnolXiCriticalLineArgument x).im =
      Real.log 2 * x := by
    rw [Complex.mul_im]
    rw [hlogre, hlogim]
    simp [burnolXiCriticalLineArgument]
  rw [hre, him, hsqrt]

private theorem two_cpow_criticalLineArgument_normSq (x : ℝ) :
    Complex.normSq ((2 : ℂ) ^ burnolXiCriticalLineArgument x) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
    Complex.normSq_eq_norm_sq,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
    burnolXiCriticalLineArgument_re, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem re_two_cpow_div_sub_one_criticalLineArgument (x : ℝ) :
    (((2 : ℂ) ^ burnolXiCriticalLineArgument x /
      ((2 : ℂ) ^ burnolXiCriticalLineArgument x - 1)).re) =
      (2 - Real.sqrt 2 * Real.cos (Real.log 2 * x)) /
        (3 - 2 * Real.sqrt 2 * Real.cos (Real.log 2 * x)) := by
  let q : ℂ := (2 : ℂ) ^ burnolXiCriticalLineArgument x
  have hqre : q.re = Real.sqrt 2 * Real.cos (Real.log 2 * x) := by
    simpa [q] using two_cpow_criticalLineArgument_re x
  have hqnorm : Complex.normSq q = 2 := by
    simpa [q] using two_cpow_criticalLineArgument_normSq x
  have hnum : q.re * (q - 1).re + q.im * (q - 1).im =
      2 - Real.sqrt 2 * Real.cos (Real.log 2 * x) := by
    rw [Complex.sub_re, Complex.sub_im]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    have hqapply : q.re * q.re + q.im * q.im = 2 := by
      simpa [Complex.normSq_apply] using hqnorm
    nlinarith
  have hden : Complex.normSq (q - 1) =
      3 - 2 * Real.sqrt 2 * Real.cos (Real.log 2 * x) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    have hqapply : q.re * q.re + q.im * q.im = 2 := by
      simpa [Complex.normSq_apply] using hqnorm
    nlinarith
  change (q / (q - 1)).re = _
  rw [Complex.div_re, hden, ← add_div, hnum]

private theorem burnolXiCompletionLogDerivative_critical_re (x : ℝ) :
    2 * (burnolXiCompletionLogDerivative (burnolXiCriticalLineArgument x)).re =
      burnolXiCompletionCriticalNormalLogEnergySlope x := by
  let w : ℂ := burnolXiCriticalLineArgument x
  let d : ℝ := x ^ 2 + 1 / 4
  have hnormw : Complex.normSq w = d := by
    dsimp [w, d]
    rw [Complex.normSq_apply]
    simp [burnolXiCriticalLineArgument]
    ring
  have hnormw1 : Complex.normSq (w - 1) = d := by
    dsimp [w, d]
    rw [Complex.normSq_apply]
    simp [burnolXiCriticalLineArgument]
    ring
  have htwo : ((2 : ℂ) / w).re = 1 / d := by
    rw [Complex.div_re, hnormw]
    dsimp [w]
    simp [burnolXiCriticalLineArgument]
  have hone : ((1 : ℂ) / (w - 1)).re = -(1 / 2) / d := by
    rw [Complex.div_re, hnormw1]
    dsimp [w]
    simp [burnolXiCriticalLineArgument]
    ring
  have hprime := re_two_cpow_div_sub_one_criticalLineArgument x
  dsimp [burnolXiCompletionLogDerivative]
  change 2 * (((2 : ℂ) / w).re + ((1 : ℂ) / (w - 1)).re -
    (((Real.log 2 : ℂ) * ((2 : ℂ) ^ w / ((2 : ℂ) ^ w - 1))).re)) = _
  rw [htwo, hone]
  have hmul :
      (((Real.log 2 : ℂ) * ((2 : ℂ) ^ w / ((2 : ℂ) ^ w - 1))).re) =
        Real.log 2 *
          (2 - Real.sqrt 2 * Real.cos (Real.log 2 * x)) /
            (3 - 2 * Real.sqrt 2 * Real.cos (Real.log 2 * x)) := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    simpa [w, mul_div_assoc] using
      congrArg (fun y : ℝ => Real.log 2 * y) hprime
  rw [hmul]
  dsimp [burnolXiCompletionCriticalNormalLogEnergySlope, d]
  ring

private theorem hasDerivAt_burnolXiCompletionMultiplier_logDerivative
    {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    HasDerivAt burnolXiCompletionMultiplier
      (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w) w := by
  have hwne0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw0
    linarith
  have hwne1 : w ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hw1
    linarith
  have hqne : (2 : ℂ) ^ w - 1 ≠ 0 := two_cpow_sub_one_ne_zero hw0
  have hid : HasDerivAt (fun z : ℂ => z) 1 w := hasDerivAt_id w
  have hq : HasDerivAt (fun z : ℂ => (2 : ℂ) ^ z)
      ((2 : ℂ) ^ w * Complex.log (2 : ℂ)) w :=
    by
      simpa only [mul_one] using
        hid.const_cpow (c := (2 : ℂ)) (Or.inl (by norm_num))
  have hnum := (hid.pow 2).mul (hid.sub_const 1)
  have hden := (hasDerivAt_const (x := w) (c := (2 : ℂ))).mul (hq.sub_const 1)
  have hquot := hnum.div hden (mul_ne_zero two_ne_zero hqne)
  have hraw : HasDerivAt burnolXiCompletionMultiplier
      (((2 * w * (w - 1) + w ^ 2) * (2 * ((2 : ℂ) ^ w - 1)) -
          (w ^ 2 * (w - 1)) * (2 * ((2 : ℂ) ^ w * Complex.log (2 : ℂ)))) /
        (2 * ((2 : ℂ) ^ w - 1)) ^ 2) w := by
    simpa only [burnolXiCompletionMultiplier, pow_two, mul_one, zero_mul, zero_add,
      Nat.cast_ofNat] using hquot
  convert hraw using 1
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  dsimp [burnolXiCompletionMultiplier, burnolXiCompletionLogDerivative]
  field_simp [hwne0, hwne1, hqne]
  ring

/-- The explicit negative function is the genuine horizontal normal derivative of the logarithmic
energy of the coefficient-faithful Burnol--Xi completion multiplier. -/
theorem hasDerivAt_burnolXiCompletion_critical_normal_logEnergy (x : ℝ) :
    HasDerivAt
      (fun σ : ℝ =>
        2 * Real.log ‖burnolXiCompletionMultiplier
          ((σ : ℂ) + Complex.I * (x : ℂ))‖)
      (burnolXiCompletionCriticalNormalLogEnergySlope x) (1 / 2) := by
  let w : ℂ := burnolXiCriticalLineArgument x
  have hwre : w.re = 1 / 2 := by simp [w, burnolXiCriticalLineArgument_re]
  have hC := hasDerivAt_burnolXiCompletionMultiplier_logDerivative
    (w := w) (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
  have hpath : HasDerivAt (fun σ : ℝ => (σ : ℂ) + Complex.I * (x : ℂ)) 1 (1 / 2) := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (1 / 2 : ℝ))).add_const
      (Complex.I * (x : ℂ))
  have hcomp : HasDerivAt
      (fun σ : ℝ => burnolXiCompletionMultiplier
        ((σ : ℂ) + Complex.I * (x : ℂ)))
      (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w) (1 / 2) := by
    have hC' : HasDerivAt burnolXiCompletionMultiplier
        (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w)
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) := by
      simpa [w, burnolXiCriticalLineArgument] using hC
    simpa only [Function.comp_apply, mul_one] using hC'.comp (1 / 2) hpath
  have hne : burnolXiCompletionMultiplier w ≠ 0 :=
    burnolXiCompletionMultiplier_ne_zero
      (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
  have hlog := hasDerivAt_log_norm_comp hcomp
    (by simpa [w, burnolXiCriticalLineArgument] using hne)
  have henergy := hlog.const_mul 2
  apply henergy.congr_deriv
  have hpoint : burnolXiCompletionMultiplier
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) = burnolXiCompletionMultiplier w := by
    simp [w, burnolXiCriticalLineArgument]
  rw [hpoint, show (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w) /
      burnolXiCompletionMultiplier w = burnolXiCompletionLogDerivative w by field_simp]
  exact burnolXiCompletionLogDerivative_critical_re x

/-- Analytic source completion is uniformly normally dissipative, in derivative form. -/
theorem deriv_burnolXiCompletion_critical_normal_logEnergy_lt_neg_half (x : ℝ) :
    deriv (fun σ : ℝ =>
      2 * Real.log ‖burnolXiCompletionMultiplier
        ((σ : ℂ) + Complex.I * (x : ℂ))‖) (1 / 2) < -(1 / 2 : ℝ) := by
  rw [(hasDerivAt_burnolXiCompletion_critical_normal_logEnergy x).deriv]
  exact burnolXiCompletionCriticalNormalLogEnergySlope_lt_neg_half x

/-! ## Exact separation of completion and source currents -/

/-- **Coefficient-faithful normal-current separation.**  For every differentiable nonzero source
path `g`, multiplication by the exact prime-two Burnol--Xi completion adds precisely the explicit
completion anomaly to the source logarithmic-energy current.  No divisor, critical-line placement,
or sign premise occurs in this identity. -/
theorem hasDerivAt_burnolXiCompletion_mul_critical_normal_logEnergy
    (x : ℝ) {g : ℝ → ℂ} {g' : ℂ}
    (hg : HasDerivAt g g' (1 / 2)) (hg0 : g (1 / 2) ≠ 0) :
    HasDerivAt
      (fun σ : ℝ =>
        2 * Real.log ‖burnolXiCompletionMultiplier
          ((σ : ℂ) + Complex.I * (x : ℂ)) * g σ‖)
      (burnolXiCompletionCriticalNormalLogEnergySlope x +
        2 * (g' / g (1 / 2)).re) (1 / 2) := by
  let w : ℂ := burnolXiCriticalLineArgument x
  have hwre : w.re = 1 / 2 := by simp [w, burnolXiCriticalLineArgument_re]
  have hC := hasDerivAt_burnolXiCompletionMultiplier_logDerivative
    (w := w) (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
  have hpath : HasDerivAt (fun σ : ℝ => (σ : ℂ) + Complex.I * (x : ℂ)) 1 (1 / 2) := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (1 / 2 : ℝ))).add_const
      (Complex.I * (x : ℂ))
  have hCpath : HasDerivAt
      (fun σ : ℝ => burnolXiCompletionMultiplier
        ((σ : ℂ) + Complex.I * (x : ℂ)))
      (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w) (1 / 2) := by
    have hC' : HasDerivAt burnolXiCompletionMultiplier
        (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w)
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) := by
      simpa [w, burnolXiCriticalLineArgument] using hC
    simpa only [Function.comp_apply, mul_one] using hC'.comp (1 / 2) hpath
  have hCne : burnolXiCompletionMultiplier w ≠ 0 :=
    burnolXiCompletionMultiplier_ne_zero
      (by rw [hwre]; norm_num) (by rw [hwre]; norm_num)
  have hsplit := hasDerivAt_two_log_norm_mul hCpath hg
    (by simpa [w, burnolXiCriticalLineArgument] using hCne) hg0
  apply hsplit.congr_deriv
  have hquot :
      (burnolXiCompletionMultiplier w * burnolXiCompletionLogDerivative w) /
          burnolXiCompletionMultiplier w =
        burnolXiCompletionLogDerivative w := by
    field_simp [hCne]
  rw [show burnolXiCompletionMultiplier
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) =
        burnolXiCompletionMultiplier w by simp [w, burnolXiCriticalLineArgument], hquot,
    burnolXiCompletionLogDerivative_critical_re]
  ring

/-! ## Reflection scattering across the critical seam -/

/-- Logarithmic energy of the coefficient-faithful completion relative to its horizontal
reflection.  This is the scalar scattering channel naturally seen by a singular Cartier boundary;
it is identically zero on the critical seam, but its transverse derivative need not vanish. -/
def burnolXiCompletionReflectionLogEnergy (x σ : ℝ) : ℝ :=
  2 * Real.log ‖burnolXiCompletionMultiplier
      ((σ : ℂ) + Complex.I * (x : ℂ))‖ -
    2 * Real.log ‖burnolXiCompletionMultiplier
      (((1 - σ : ℝ) : ℂ) + Complex.I * (x : ℂ))‖

/-- The reflection-scattering current doubles the one-sided normal current: reflection reverses
the parameter derivative, so subtraction changes the second sign. -/
theorem hasDerivAt_burnolXiCompletionReflectionLogEnergy (x : ℝ) :
    HasDerivAt (burnolXiCompletionReflectionLogEnergy x)
      (2 * burnolXiCompletionCriticalNormalLogEnergySlope x) (1 / 2) := by
  let E : ℝ → ℝ := fun σ =>
    2 * Real.log ‖burnolXiCompletionMultiplier
      ((σ : ℂ) + Complex.I * (x : ℂ))‖
  have hE : HasDerivAt E
      (burnolXiCompletionCriticalNormalLogEnergySlope x) (1 / 2) := by
    simpa only [E] using hasDerivAt_burnolXiCompletion_critical_normal_logEnergy x
  have hreflect : HasDerivAt (fun σ : ℝ => 1 - σ) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have hcomp := hE.comp (1 / 2) hreflect
  have hsub := hE.sub hcomp
  convert hsub using 1 <;>
    simp only [burnolXiCompletionReflectionLogEnergy, E, Function.comp_apply] <;> ring

/-- **Strict reflected source orientation.**  The exact prime-two completion scattering loses
more than one full logarithmic-energy unit when crossing the critical seam toward the right. -/
theorem deriv_burnolXiCompletionReflectionLogEnergy_lt_neg_one (x : ℝ) :
    deriv (burnolXiCompletionReflectionLogEnergy x) (1 / 2) < -1 := by
  rw [(hasDerivAt_burnolXiCompletionReflectionLogEnergy x).deriv]
  nlinarith [burnolXiCompletionCriticalNormalLogEnergySlope_lt_neg_half x]

end RHTower
