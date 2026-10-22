import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.LagExplicitFormula
import GaloisForLFunctions.RHTower.CCM.CCMSourceDivisorEnergySpectrum

/-!
# Quantitative tails of the zero weights

The weights `w_q = 1/(q(1−q))` of the Xi zero copies have a quantitative tail
(`tsum_indicator_abs_im_gt_weight_le`):

`Σ_{|Im q| > T} |w_q| ≤ 80 (C + log(3T + 4))/T`   for `T ≥ 1`,

with `C` the corpus line-two constant.  For `|Im q| ≥ 1` the weight is at most twice the Lorentzian
term `1/(1 + (Im q)²)`; the zeros above `T` are counted by the width-`√(1+T²)` Lorentzian mass at
`T`, and those below `−T` by the same mass at `0`, since `1/(1+γ²) ≤ 4/(1 + (T − γ)²)` for
`γ ≤ −T`.  Both masses are `O(log T / T)`.

Also: under `XiZeroHalfPlaneBound α` every copy satisfies `|Re q − ½| ≤ α`
(`abs_re_sub_half_le_of_xiZeroHalfPlaneBound`).
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Under a half-plane bound the zeros lie in the symmetric strip `|Re q − ½| ≤ α`. -/
theorem abs_re_sub_half_le_of_xiZeroHalfPlaneBound {alpha : ℝ} (hXi : XiZeroHalfPlaneBound alpha)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ alpha := by
  have h1 := hXi _ (xi_xiZeroCopy_eq_zero q)
  have h2 := hXi _ (xi_xiZeroCopy_eq_zero (xiZeroCopyReflectEquiv q))
  rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]
  constructor <;> linarith

/-- `‖q(1−q)‖ ≥ (Im q)²`. -/
theorem sq_im_le_norm_mul_one_sub (s : ℂ) : s.im ^ 2 ≤ ‖s * (1 - s)‖ := by
  rw [norm_mul]
  have h1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have h2 : |s.im| ≤ ‖1 - s‖ := by
    have := Complex.abs_im_le_norm (1 - s)
    rwa [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at this
  rw [← sq_abs]
  exact pow_two |s.im| ▸ mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- For `|Im s| ≥ 1`, `‖1/(s(1−s))‖ ≤ 2/(1 + (Im s)²)`. -/
theorem norm_one_div_mul_one_sub_le {s : ℂ} (hs : 1 ≤ |s.im|) :
    ‖1 / (s * (1 - s))‖ ≤ 2 / (1 + s.im ^ 2) := by
  have hsq : 1 ≤ s.im ^ 2 := by rw [← sq_abs]; nlinarith
  have hpos : 0 < ‖s * (1 - s)‖ := lt_of_lt_of_le (by linarith) (sq_im_le_norm_mul_one_sub s)
  rw [norm_div, norm_one, div_le_div_iff₀ hpos (by positivity)]
  have := sq_im_le_norm_mul_one_sub s
  nlinarith

/-- **The weight tail.** -/
theorem tsum_indicator_abs_im_gt_weight_le {T : ℝ} (hT : 1 ≤ T) :
    ∑' q : XiZeroCopy, {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
        (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q
      ≤ 80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T := by
  classical
  set w : ℝ := Real.sqrt (1 + T ^ 2) with hw
  have hw1 : 1 ≤ w := by
    rw [hw, Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have hwT : T ≤ w := by
    rw [hw, Real.le_sqrt (by linarith) (by positivity)]; nlinarith
  have hwT' : w ≤ T + 1 := by
    rw [hw, Real.sqrt_le_left (by linarith)]; nlinarith
  have hT0 : 0 < T := by linarith
  -- pointwise domination
  have hdom : ∀ q : XiZeroCopy,
      {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q ≤
        2 * {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm 0) q +
          8 * {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm T) q := by
    intro q
    unfold Set.indicator
    by_cases h : T < |(q.1 : ℂ).im|
    · rw [if_pos (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from h)]
      have hw2 := norm_one_div_mul_one_sub_le (s := (q.1 : ℂ)) (by linarith)
      rcases le_or_gt 0 (q.1 : ℂ).im with hpos | hneg
      · have hgt : T < (q.1 : ℂ).im := by rwa [abs_of_nonneg hpos] at h
        rw [if_pos (show q ∈ {q : XiZeroCopy | T < (q.1 : ℂ).im} from hgt),
          if_neg (show q ∉ {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0} by
            simp only [Set.mem_setOf_eq, not_le]; linarith)]
        have : 2 / (1 + (q.1 : ℂ).im ^ 2) = 2 * lorentzMassTerm 0 q := by
          unfold lorentzMassTerm; ring
        beta_reduce
        linarith
      · have hlt : (q.1 : ℂ).im < -T := by rw [abs_of_neg hneg] at h; linarith
        rw [if_neg (show q ∉ {q : XiZeroCopy | T < (q.1 : ℂ).im} by
          simp only [Set.mem_setOf_eq, not_lt]; linarith),
          if_pos (show q ∈ {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0} from hneg.le)]
        have hL : 2 / (1 + (q.1 : ℂ).im ^ 2) ≤ 8 * lorentzMassTerm T q := by
          unfold lorentzMassTerm
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        beta_reduce
        linarith
    · rw [if_neg (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from h)]
      have h1 : 0 ≤ 2 * {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm 0) q :=
        mul_nonneg (by norm_num) (Set.indicator_nonneg (fun q _ => lorentzMassTerm_nonneg 0 q) q)
      have h2 : 0 ≤ 8 * {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm T) q :=
        mul_nonneg (by norm_num) (Set.indicator_nonneg (fun q _ => lorentzMassTerm_nonneg T q) q)
      simp only [Set.indicator] at h1 h2
      linarith
  have hs1 := ((summable_lorentzMassTerm 0).indicator
    {q : XiZeroCopy | T < (q.1 : ℂ).im}).mul_left 2
  have hs2 := ((summable_lorentzMassTerm T).indicator
    {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}).mul_left 8
  have hsw : Summable (fun q : XiZeroCopy => {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
      (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q) :=
    summable_inv_mul_one_sub.norm.indicator _
  refine (Summable.tsum_le_tsum hdom hsw (hs1.add hs2)).trans ?_
  rw [Summable.tsum_add hs1 hs2, tsum_mul_left, tsum_mul_left]
  have e1 := tsum_indicator_gt_le_lorentzMassW (t := 0) (T := T) hT0.le
  have e2 := tsum_indicator_le_zero_le_lorentzMassW (t := T) hT0.le
  rw [sub_zero, ← hw] at e1
  rw [← hw] at e2
  have m1 := lorentzMassW_le_log hw1 T
  have m2 := lorentzMassW_le_log hw1 0
  rw [abs_of_pos hT0] at m1
  rw [abs_zero, add_zero] at m2
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hl1 : Real.log (w + T + 4) ≤ Real.log (3 * T + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log (w + 4) ≤ Real.log (3 * T + 4) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog0 : 0 ≤ Real.log (3 * T + 4) := Real.log_nonneg (by linarith)
  have hlogw1 : 0 ≤ Real.log (w + T + 4) := Real.log_nonneg (by linarith)
  have hlogw2 : 0 ≤ Real.log (w + 4) := Real.log_nonneg (by linarith)
  have h8w : 8 / w ≤ 8 / T := div_le_div_of_nonneg_left (by norm_num) hT0 hwT
  have hb1 : lorentzMassW w T ≤ 8 / T * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) :=
    m1.trans (mul_le_mul h8w (by linarith) (by linarith) (by positivity))
  have hb2 : lorentzMassW w 0 ≤ 8 / T * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) :=
    m2.trans (mul_le_mul h8w (by linarith) (by linarith) (by positivity))
  calc 2 * ∑' q : XiZeroCopy, {q : XiZeroCopy | T < (q.1 : ℂ).im}.indicator (lorentzMassTerm 0) q +
        8 * ∑' q : XiZeroCopy, {q : XiZeroCopy | (q.1 : ℂ).im ≤ 0}.indicator (lorentzMassTerm T) q
      ≤ 2 * (8 / T * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4))) +
          8 * (8 / T * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4))) := by
        gcongr
        · exact e1.trans hb1
        · exact e2.trans hb2
    _ = 80 * (xiLineTwoLogDerivConstant + Real.log (3 * T + 4)) / T := by
        field_simp
        ring

end

end RHTower
