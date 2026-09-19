import GaloisForLFunctions.RHTower.WeilInsertionAnyWeight

/-!
# The zero side of the modulated bump at a frequency in a gap of the zeros

When every spectral point is real and at distance at least `d > 0` from the modulation frequency
`ζ`, the zero-side sum of the modulated wide bump is `O(L^{-4})` with a constant depending only on
`ζ` and `d`: the finitely many spectral points below `2|ζ| + 1` contribute through the gap, the
others through the cubic decay of the transform.  This removes the restriction `|ζ| ≤ 31/10` of the
single-insertion argument and lets the modulation frequency range over the whole complement of the
(closed, discrete) set of zero ordinates.
-/

open MeasureTheory Set Filter Topology Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-- The gap constant `max((2|ζ|+1)²/d⁶, 64)`. -/
def gapConstant (ζ d : ℝ) : ℝ := max ((2 * |ζ| + 1) ^ 2 / d ^ 6) 64

theorem gapConstant_pos (ζ d : ℝ) : 0 < gapConstant ζ d :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem normSq_paperFT_modulatedBump_le_of_gap {L : ℝ} (hL : 1 ≤ L) {ζ d : ℝ} (hd : 0 < d)
    (q : XiZeroCopy) (hq : (xiSpectralPoint q).im = 0)
    (hgap : d ≤ |ζ - (xiSpectralPoint q).re|) :
    ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
      kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re with hr
  have hz : -xiSpectralPoint q = ((-r : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [hq]
  have hnormsq : ‖xiSpectralPoint q‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hq, hr]
    ring
  have hr2 : 41 / 2 < r ^ 2 := by
    rw [← hnormsq]
    exact fortyOne_div_two_lt_normSq_spectralPoint q
  have hgap' : d ≤ |-r + ζ| := by
    rw [show -r + ζ = ζ - r by ring]
    exact hgap
  have hne : -r + ζ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hgap'
    linarith
  have hpos : 0 < |-r + ζ| := abs_pos.mpr hne
  have hk := kappaThree_pos
  have hL4 : 0 < L ^ 4 := by positivity
  have hr2pos : 0 < r ^ 2 := by linarith
  rw [hz]
  have hb := norm_paperFT_modulatedBump_le hL (r := -r) hne
  have hsq : ‖Zeta23.paperFT (modulatedBump L ζ) ((-r : ℝ) : ℂ)‖ ^ 2 ≤
      kappaThree ^ 2 / L ^ 4 * (1 / |-r + ζ| ^ 6) := by
    calc ‖Zeta23.paperFT (modulatedBump L ζ) ((-r : ℝ) : ℂ)‖ ^ 2
        ≤ (kappaThree / (L ^ 2 * |-r + ζ| ^ 3)) ^ 2 := by gcongr
      _ = kappaThree ^ 2 / L ^ 4 * (1 / |-r + ζ| ^ 6) := by
          field_simp
  have habs6 : |r| ^ 6 = r ^ 2 * (r ^ 2) ^ 2 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs]
    ring
  have hkey : 1 / |-r + ζ| ^ 6 ≤ gapConstant ζ d / r ^ 2 := by
    by_cases hbig : |r| ≤ 2 * |ζ| + 1
    · have h1 : 1 / |-r + ζ| ^ 6 ≤ 1 / d ^ 6 := by gcongr
      have h2 : r ^ 2 ≤ (2 * |ζ| + 1) ^ 2 := by
        rw [← sq_abs r]
        gcongr
      have hd6 : 0 < d ^ 6 := by positivity
      calc 1 / |-r + ζ| ^ 6 ≤ 1 / d ^ 6 := h1
        _ ≤ (2 * |ζ| + 1) ^ 2 / d ^ 6 / r ^ 2 := by
            rw [div_div, div_le_div_iff₀ hd6 (by positivity)]
            nlinarith
        _ ≤ gapConstant ζ d / r ^ 2 := by
            gcongr
            exact le_max_left _ _
    · push Not at hbig
      have h1 : |r| / 2 ≤ |-r + ζ| := by
        have := abs_sub_abs_le_abs_sub (-r) (-ζ)
        rw [abs_neg, abs_neg, sub_neg_eq_add] at this
        linarith
      have hrpos : 0 < |r| := by linarith [abs_nonneg ζ]
      have h2 : 1 / |-r + ζ| ^ 6 ≤ 64 / |r| ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := pow_le_pow_left₀ (by positivity) h1 6
        rw [div_pow] at this
        norm_num at this
        linarith
      have h3 : 1 ≤ (r ^ 2) ^ 2 := by nlinarith
      calc 1 / |-r + ζ| ^ 6 ≤ 64 / |r| ^ 6 := h2
        _ ≤ 64 / r ^ 2 := by
            rw [habs6]
            gcongr
            nlinarith
        _ ≤ gapConstant ζ d / r ^ 2 := by
            gcongr
            exact le_max_right _ _
  calc ‖Zeta23.paperFT (modulatedBump L ζ) ((-r : ℝ) : ℂ)‖ ^ 2
      ≤ kappaThree ^ 2 / L ^ 4 * (1 / |-r + ζ| ^ 6) := hsq
    _ ≤ kappaThree ^ 2 / L ^ 4 * (gapConstant ζ d / r ^ 2) := by gcongr
    _ = kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [hnormsq]
        ring

/-- The zero-side constant at a gap frequency. -/
def gapZeroSideConstant (ζ d : ℝ) : ℝ := kappaThree ^ 2 * gapConstant ζ d * (33 / 100)

theorem gapZeroSideConstant_pos (ζ d : ℝ) : 0 < gapZeroSideConstant ζ d := by
  unfold gapZeroSideConstant
  have := kappaThree_pos
  have := gapConstant_pos ζ d
  positivity

/-- **The zero side of the modulated bump at a gap frequency is `O(L⁻⁴)`.** -/
theorem tsum_normSq_paperFT_modulatedBump_le_of_gap
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0)
    {L : ℝ} (hL : 1 ≤ L) {ζ d : ℝ} (hd : 0 < d)
    (hgap : ∀ q : XiZeroCopy, d ≤ |ζ - (xiSpectralPoint q).re|) :
    ∑' q : XiZeroCopy, ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
      gapZeroSideConstant ζ d / L ^ 4 := by
  have hsum : Summable (fun q : XiZeroCopy =>
      kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hle : ∀ q : XiZeroCopy,
      ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
        kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    fun q => normSq_paperFT_modulatedBump_le_of_gap hL hd q (hreal q) (hgap q)
  have hsum' : Summable (fun q : XiZeroCopy =>
      ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun q => by positivity) hle hsum
  have hL4 : 0 < L ^ 4 := by positivity
  have hk := kappaThree_pos
  have hg := gapConstant_pos ζ d
  calc ∑' q : XiZeroCopy, ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2
      ≤ ∑' q : XiZeroCopy,
          kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
        Summable.tsum_le_tsum hle hsum' hsum
    _ = kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
        tsum_mul_left
    _ ≤ kappaThree ^ 2 * gapConstant ζ d / L ^ 4 * (33 / 100) := by
        gcongr
        exact tsum_inv_normSq_spectralPoint_lt.le
    _ = gapZeroSideConstant ζ d / L ^ 4 := by
        unfold gapZeroSideConstant
        ring

end RHTower.WeilDeletion

end
