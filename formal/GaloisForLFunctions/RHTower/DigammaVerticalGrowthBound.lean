import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth

/-!
# A two-sided logarithmic bound for the digamma real part on a vertical line

Below unit height the real part is trapped between its value on the real axis and its value at
height one, because it is monotone in the height.  Above unit height the unconditional vertical
digamma bound compares it with `½ log(σ² + t²)`, whose error terms `1/t² + π/(2t)` are then
absolutely bounded.  Together:

`|Re psi(c + i y)| ≤ K(c) + log (2 + |y|)`

with an explicit constant.  This is the companion upper bound to the archimedean coercivity, and it
is what makes a logarithmic archimedean rate integrable against a rational half-density.
-/

open Complex

noncomputable section

namespace RHTower

/-- The archimedean growth constant of the vertical digamma line. -/
def digammaVerticalGrowthConst (c : ℝ) : ℝ :=
  |(Complex.digamma ((c : ℂ))).re|
    + |(Complex.digamma ((c : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).re|
    + Real.log (c + 1) + 1 + Real.pi / 2

theorem digammaVerticalGrowthConst_nonneg {c : ℝ} (hc : 0 < c) :
    0 ≤ digammaVerticalGrowthConst c := by
  have hlog : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ |(Complex.digamma ((c : ℂ))).re| := abs_nonneg _
  have h2 : 0 ≤ |(Complex.digamma ((c : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).re| := abs_nonneg _
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  unfold digammaVerticalGrowthConst
  linarith

/-- The real part of digamma on a vertical line depends only on the absolute height. -/
theorem re_digamma_vertical_abs {c : ℝ} (hc : 0 < c) (y : ℝ) :
    (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re
      = (Complex.digamma ((c : ℂ) + ((|y| : ℝ) : ℂ) * Complex.I)).re := by
  refine le_antisymm (re_digamma_mono_of_abs_le hc ?_) (re_digamma_mono_of_abs_le hc ?_)
  · rw [abs_abs]
  · rw [abs_abs]

/-- **Two-sided archimedean growth.**  The real part of digamma on a vertical line grows at most
logarithmically in the height. -/
theorem abs_re_digamma_vertical_le {c : ℝ} (hc : 0 < c) (y : ℝ) :
    |(Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re|
      ≤ digammaVerticalGrowthConst c + Real.log (2 + |y|) := by
  have hlog2 : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by
    have := abs_nonneg y
    linarith)
  have hlogc : 0 ≤ Real.log (c + 1) := Real.log_nonneg (by linarith)
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hA : 0 ≤ |(Complex.digamma ((c : ℂ))).re| := abs_nonneg _
  have hB : 0 ≤ |(Complex.digamma ((c : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).re| := abs_nonneg _
  rcases le_or_gt |y| 1 with hy | hy
  · -- small height: monotonicity traps the value between two constants
    have hzero : (Complex.digamma ((c : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)).re
        = (Complex.digamma ((c : ℂ))).re := by
      norm_num
    have hlow : (Complex.digamma ((c : ℂ))).re
        ≤ (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re := by
      rw [← hzero]
      refine re_digamma_mono_of_abs_le hc ?_
      simp [abs_nonneg y]
    have hhigh : (Complex.digamma ((c : ℂ) + (y : ℂ) * Complex.I)).re
        ≤ (Complex.digamma ((c : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).re := by
      refine re_digamma_mono_of_abs_le hc ?_
      rw [abs_one]
      exact hy
    have h1 := le_abs_self (Complex.digamma ((c : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).re
    have h2 := neg_abs_le (Complex.digamma ((c : ℂ))).re
    rw [abs_le]
    unfold digammaVerticalGrowthConst
    constructor <;> linarith
  · -- large height: the unconditional vertical bound
    have hy0 : (0 : ℝ) < |y| := by linarith
    have habs := re_digamma_vertical_abs hc y
    have hb := re_digamma_vertical_bound_uncond (σ := c) (t := |y|) hc.le hy0
    have hb' := abs_le.mp hb
    have herr : 1 / |y| ^ 2 + Real.pi / (2 * |y|) ≤ 1 + Real.pi / 2 := by
      have h1 : 1 / |y| ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
      have h2 : Real.pi / (2 * |y|) ≤ Real.pi / 2 := by
        refine div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) ?_
        linarith
      linarith
    -- the logarithm of the modulus is controlled by `log (c+1) + log (2+|y|)`
    have hmodub : (1 / 2) * Real.log (c ^ 2 + |y| ^ 2) ≤ Real.log (c + 1) + Real.log (2 + |y|) := by
      have hprod : c ^ 2 + |y| ^ 2 ≤ ((c + 1) * (2 + |y|)) ^ 2 := by
        nlinarith [abs_nonneg y, sq_nonneg (c + |y|)]
      have hpos : (0 : ℝ) < (c + 1) * (2 + |y|) := by positivity
      have hlogle : Real.log (c ^ 2 + |y| ^ 2) ≤ Real.log (((c + 1) * (2 + |y|)) ^ 2) := by
        refine Real.log_le_log (by positivity) hprod
      rw [Real.log_pow, Real.log_mul (by positivity) (by positivity)] at hlogle
      push_cast at hlogle
      linarith
    have hmodlb : (0 : ℝ) ≤ (1 / 2) * Real.log (c ^ 2 + |y| ^ 2) := by
      have h1 : (1 : ℝ) ≤ c ^ 2 + |y| ^ 2 := by nlinarith
      have := Real.log_nonneg h1
      linarith
    rw [habs, abs_le]
    unfold digammaVerticalGrowthConst
    constructor <;> linarith [hb'.1, hb'.2]

end RHTower

end
