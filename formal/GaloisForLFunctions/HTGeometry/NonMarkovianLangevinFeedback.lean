import GaloisForLFunctions.HTGeometry.NonMarkovianLangevinKernel
import Mathlib.Tactic

open scoped NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Paper's below-threshold central-linewidth law, with all physical parameters nonnegative. -/
def subthresholdNarrowedLinewidth
    (baseline feedback delay : ℝ≥0) : ℝ :=
  (baseline : ℝ) / Real.sqrt
    ((1 + (feedback : ℝ)) ^ 2 +
      (feedback : ℝ) * (baseline : ℝ) * (delay : ℝ) / 2)

theorem subthresholdNarrowedLinewidth_le_linear
    (baseline feedback delay : ℝ≥0) :
    subthresholdNarrowedLinewidth baseline feedback delay ≤
      (baseline : ℝ) / (1 + (feedback : ℝ)) := by
  unfold subthresholdNarrowedLinewidth
  have hfb : 0 ≤ (feedback : ℝ) := feedback.property
  have hbase : 0 ≤ (baseline : ℝ) := baseline.property
  have hdelay : 0 ≤ (delay : ℝ) := delay.property
  have hsquare : 0 ≤ (1 + (feedback : ℝ)) ^ 2 := sq_nonneg _
  have hradicand : 0 ≤ (1 + (feedback : ℝ)) ^ 2 +
      (feedback : ℝ) * (baseline : ℝ) * (delay : ℝ) / 2 := by positivity
  have hsqrt : 1 + (feedback : ℝ) ≤ Real.sqrt
      ((1 + (feedback : ℝ)) ^ 2 +
        (feedback : ℝ) * (baseline : ℝ) * (delay : ℝ) / 2) := by
    rw [Real.le_sqrt (by positivity) hradicand]
    nlinarith [mul_nonneg (mul_nonneg hfb hbase) hdelay]
  exact div_le_div_of_nonneg_left hbase (by positivity) hsqrt

theorem subthresholdNarrowedLinewidth_le_baseline
    (baseline feedback delay : ℝ≥0) :
    subthresholdNarrowedLinewidth baseline feedback delay ≤ baseline := by
  refine (subthresholdNarrowedLinewidth_le_linear baseline feedback delay).trans ?_
  exact (div_le_iff₀ (by positivity : 0 < 1 + (feedback : ℝ))).2
    (by nlinarith [baseline.property, feedback.property])

theorem subthresholdNarrowedLinewidth_zero_feedback
    (baseline delay : ℝ≥0) :
    subthresholdNarrowedLinewidth baseline 0 delay = baseline := by
  simp [subthresholdNarrowedLinewidth, Real.sqrt_one]

theorem quadraticNarrowedLinewidth_le_linear
    (baseline feedback : ℝ≥0) :
    quadraticNarrowedLinewidth baseline feedback ≤
      (baseline : ℝ) / (1 + (feedback : ℝ)) := by
  unfold quadraticNarrowedLinewidth
  have hbase : 0 ≤ (baseline : ℝ) := baseline.property
  have hden : 0 < 1 + (feedback : ℝ) := by positivity
  exact div_le_div_of_nonneg_left hbase hden
    (by nlinarith [feedback.property])

/-- Exact denominator of the paper's linear delayed-feedback transfer function. -/
def delayedFeedbackTransferDenominator
    (frequency : ℝ) (damping feedback delay : ℝ≥0) : ℂ :=
  Complex.I * (frequency : ℂ) + (damping : ℂ) +
    (feedback : ℂ) *
      (1 - Complex.exp (((-frequency * (delay : ℝ) : ℝ) : ℂ) * Complex.I))

theorem normSq_delayedFeedbackTransferDenominator
    (frequency : ℝ) (damping feedback delay : ℝ≥0) :
    Complex.normSq
      (delayedFeedbackTransferDenominator frequency damping feedback delay) =
      ((damping : ℝ) + (feedback : ℝ) *
          (1 - Real.cos (frequency * (delay : ℝ)))) ^ 2 +
        (frequency + (feedback : ℝ) *
          Real.sin (frequency * (delay : ℝ))) ^ 2 := by
  unfold delayedFeedbackTransferDenominator
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im,
    Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp only [neg_mul, Real.cos_neg, Real.sin_neg]
  ring

@[simp]
theorem delayedFeedbackTransferDenominator_zero
    (damping feedback delay : ℝ≥0) :
    delayedFeedbackTransferDenominator 0 damping feedback delay = damping := by
  simp [delayedFeedbackTransferDenominator]

theorem normSq_delayedFeedbackTransferDenominator_ge_damping_sq
    (frequency : ℝ) (damping feedback delay : ℝ≥0) :
    (damping : ℝ) ^ 2 ≤
      Complex.normSq
        (delayedFeedbackTransferDenominator frequency damping feedback delay) := by
  rw [normSq_delayedFeedbackTransferDenominator]
  have hcos : Real.cos (frequency * (delay : ℝ)) ≤ 1 := Real.cos_le_one _
  have hreal : (damping : ℝ) ≤
      (damping : ℝ) + (feedback : ℝ) *
        (1 - Real.cos (frequency * (delay : ℝ))) := by
    nlinarith [feedback.property]
  nlinarith [damping.property, sq_nonneg
    (frequency + (feedback : ℝ) * Real.sin (frequency * (delay : ℝ)))]

end

end GaloisForLFunctions.HTGeometry

