import GaloisForLFunctions.RHTower.PaperEGCVerticalMajorant
import GaloisForLFunctions.RHTower.XiWallLogDerivativeCones
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# The complete EGC correction on vertical observation lines

The entire multiplicity-copy row converges with one summable budget for every allowed
shift, real source offset and imaginary height. It is continuous, decays at both infinite
ends of each fixed vertical line, and remains strictly negative at the centered observation.
These are fixed-window statements; the outer expanding-contour obligation is separate.
-/

namespace RHTower

noncomputable section
open Filter
open scoped Topology BigOperators

/-- The complete correction retains every native Xi multiplicity copy. -/
def paperEGCCompleteCorrection (eps x : PaperEGCSmallParameter) (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, paperEGCLineCopy eps x t q

/-- Continuity of each literal summand follows from certified pole avoidance. -/
theorem continuous_paperEGCLineCopy (eps x : PaperEGCSmallParameter) (q : XiZeroCopy) :
    Continuous (fun t : ℝ => paperEGCLineCopy eps x t q) := by
  have hw : Continuous (fun t : ℝ => ((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I)
  unfold paperEGCLineCopy meromorphicCauchyPairShiftResidueCorrection
  exact (continuous_const.div
    (continuous_const.mul ((continuous_const.sub hw).sub continuous_const))
    (fun t => mul_ne_zero (by norm_num) (paperEGC_line_minus_ne_zero eps x t q))).add
    (continuous_const.div
      (continuous_const.mul ((continuous_const.sub hw).add continuous_const))
      (fun t => mul_ne_zero (by norm_num) (paperEGC_line_plus_ne_zero eps x t q)))

/-- One uniform copy exhaustion works over the whole unbounded source cylinder. -/
theorem tendstoUniformly_paperEGCCompleteCorrection :
    TendstoUniformly
      (fun S : Finset XiZeroCopy => fun p : PaperEGCSmallParameter × PaperEGCSmallParameter × ℝ =>
        ∑ q ∈ S, paperEGCLineCopy p.1 p.2.1 p.2.2 q)
      (fun p => paperEGCCompleteCorrection p.1 p.2.1 p.2.2) atTop := by
  apply tendstoUniformly_tsum
    (show Summable (fun q : XiZeroCopy => 8 / ‖xiSpectralPoint q‖^2) from
      by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
  intro q p
  exact norm_paperEGCLineCopy_le p.1 p.2.1 p.2.2 q

/-- The full correction has a continuous literal representative at every height. -/
theorem continuous_paperEGCCompleteCorrection (eps x : PaperEGCSmallParameter) :
    Continuous (paperEGCCompleteCorrection eps x) := by
  apply continuous_tsum (fun q => continuous_paperEGCLineCopy eps x q)
    (show Summable (fun q : XiZeroCopy => 8 / ‖xiSpectralPoint q‖^2) from
      by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
  intro q t
  exact norm_paperEGCLineCopy_le eps x t q

/-- The complete row preserves the quadratic small-shift budget. -/
theorem norm_paperEGCCompleteCorrection_le (eps x : PaperEGCSmallParameter) (t : ℝ) :
    ‖paperEGCCompleteCorrection eps x t‖ ≤
      (8 * (eps : ℝ)^2) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖^2 := by
  have hdom : Summable (fun q : XiZeroCopy => 8 * (eps : ℝ)^2 / ‖xiSpectralPoint q‖^2) := by
    simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left (8 * (eps : ℝ)^2)
  calc ‖paperEGCCompleteCorrection eps x t‖
      ≤ ∑' q : XiZeroCopy, ‖paperEGCLineCopy eps x t q‖ :=
        norm_tsum_le_tsum_norm (summable_norm_paperEGCLineCopy eps x t)
    _ ≤ ∑' q : XiZeroCopy, 8 * (eps : ℝ)^2 / ‖xiSpectralPoint q‖^2 :=
      Summable.tsum_le_tsum (fun q => norm_paperEGCLineCopy_le_scale eps x t q)
        (summable_norm_paperEGCLineCopy eps x t) hdom
    _ = _ := by rw [← tsum_mul_left]; congr 1; funext q; ring

private theorem inverse_vertical_tendsto_zero (a : ℂ) :
    Tendsto (fun t : ℝ => (a - (t : ℂ) * Complex.I)⁻¹)
      (Bornology.cobounded ℝ) (𝓝 0) := by
  have hline : Tendsto (fun t : ℝ => (t : ℂ) * Complex.I)
      (Bornology.cobounded ℝ) (Bornology.cobounded ℂ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real] using
      (tendsto_norm_cobounded_atTop (E := ℝ))
  exact Filter.tendsto_inv₀_cobounded.comp ((tendsto_const_sub_cobounded a).comp hline)

/-- Each actual correction decays at both infinite ends of its vertical observation line. -/
theorem tendsto_paperEGCLineCopy_cobounded (eps x : PaperEGCSmallParameter) (q : XiZeroCopy) :
    Tendsto (fun t : ℝ => paperEGCLineCopy eps x t q) (Bornology.cobounded ℝ) (𝓝 0) := by
  have hm := (inverse_vertical_tendsto_zero
    (xiSpectralPoint q - ((x : ℝ) : ℂ) - ((eps : ℝ) : ℂ))).const_mul
      (-((eps : ℝ) : ℂ) / 2)
  have hp := (inverse_vertical_tendsto_zero
    (xiSpectralPoint q - ((x : ℝ) : ℂ) + ((eps : ℝ) : ℂ))).const_mul
      (((eps : ℝ) : ℂ) / 2)
  convert hm.add hp using 1
  · funext t
    have hem : xiSpectralPoint q - (((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) -
        ((eps : ℝ) : ℂ) = xiSpectralPoint q - ((x : ℝ) : ℂ) -
          ((eps : ℝ) : ℂ) - (t : ℂ) * Complex.I := by ring
    have hep : xiSpectralPoint q - (((x : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
        ((eps : ℝ) : ℂ) = xiSpectralPoint q - ((x : ℝ) : ℂ) +
          ((eps : ℝ) : ℂ) - (t : ℂ) * Complex.I := by ring
    rw [paperEGCLineCopy, meromorphicCauchyPairShiftResidueCorrection, hem, hep]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · simp

/-- Absolute copy control permits the complete row to decay without discarding any copy. -/
theorem tendsto_paperEGCCompleteCorrection_cobounded (eps x : PaperEGCSmallParameter) :
    Tendsto (paperEGCCompleteCorrection eps x) (Bornology.cobounded ℝ) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence
    (show Summable (fun q : XiZeroCopy => 8 / ‖xiSpectralPoint q‖^2) from
      by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
    (fun q => tendsto_paperEGCLineCopy_cobounded eps x q)
    (Eventually.of_forall fun t q => norm_paperEGCLineCopy_le eps x t q)
  change Tendsto (fun t => ∑' q : XiZeroCopy, paperEGCLineCopy eps x t q)
    (Bornology.cobounded ℝ) (𝓝 0)
  simpa only [tsum_zero] using h

/-- A prescribed positive small-shift sequence, independent of the Xi divisor. -/
def paperEGCScale (n : ℕ) : PaperEGCSmallParameter :=
  ⟨((n : ℝ) + 1)⁻¹, by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    constructor
    · linarith [inv_pos.mpr hn]
    · exact (inv_le_one₀ hn).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))⟩

theorem paperEGCScale_pos (n : ℕ) : 0 < (paperEGCScale n : ℝ) := by
  exact inv_pos.mpr (by positivity)

/-- The centered source observation, fixed before any divisor expansion. -/
def paperEGCZeroOffset : PaperEGCSmallParameter := ⟨0, by constructor <;> norm_num⟩

/-- The entire infinite correction retains the strict centered obstruction. -/
theorem paperEGCCompleteCorrection_centered_re_neg (n : ℕ) :
    (paperEGCCompleteCorrection (paperEGCScale n) paperEGCZeroOffset 0).re < 0 := by
  have hs := (summable_norm_paperEGCLineCopy (paperEGCScale n) paperEGCZeroOffset 0).of_norm
  have hn (q : XiZeroCopy) :
      (paperEGCLineCopy (paperEGCScale n) paperEGCZeroOffset 0 q).re < 0 := by
    simpa only [paperEGCLineCopy, paperEGCZeroOffset, Complex.ofReal_zero,
      zero_mul, add_zero] using
      meromorphicCauchyPairShiftResidueCorrection_allCopy_centered_re_neg
        (paperEGCScale_pos n) (paperEGCScale n).2.2 q
  rw [paperEGCCompleteCorrection, Complex.re_tsum hs]
  have h := Summable.tsum_lt_tsum (fun q => (hn q).le)
    (hn (Classical.choice exists_xiZeroCopy)) (Complex.hasSum_re hs.hasSum).summable
    (summable_zero : Summable (fun _ : XiZeroCopy => (0 : ℝ)))
  simpa only [tsum_zero] using h

end
end RHTower
