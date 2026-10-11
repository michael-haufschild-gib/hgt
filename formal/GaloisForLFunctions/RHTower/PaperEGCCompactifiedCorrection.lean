import GaloisForLFunctions.RHTower.PaperEGCCompactifiedCopy
import GaloisForLFunctions.RHTower.PaperEGCCompleteCorrection

/-!
# A continuous compactification of the complete EGC correction

One summable copy budget remains valid across the projective point. Consequently the complete
correction, with every analytic multiplicity retained, is a continuous periodic profile. Its
infinity value is zero, while its centered value is strictly negative at every prescribed scale.
-/

namespace RHTower

noncomputable section
open Filter
open scoped Topology BigOperators

/-- The full compactified row, summing every Xi copy before any Fourier cutoff. -/
def paperEGCCompactifiedCorrection (eps x : PaperEGCSmallParameter) (θ : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, paperEGCCircleCopy eps x θ q

theorem summable_norm_paperEGCCircleCopy (eps x : PaperEGCSmallParameter) (θ : ℝ) :
    Summable (fun q : XiZeroCopy => ‖paperEGCCircleCopy eps x θ q‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _)
    (fun q => norm_paperEGCCircleCopy_le eps x θ q)
  simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8

/-- Copy exhaustion is uniform over all allowed shifts, offsets and compactified heights. -/
theorem tendstoUniformly_paperEGCCompactifiedCorrection :
    TendstoUniformly
      (fun S : Finset XiZeroCopy => fun p : PaperEGCSmallParameter × PaperEGCSmallParameter × ℝ =>
        ∑ q ∈ S, paperEGCCircleCopy p.1 p.2.1 p.2.2 q)
      (fun p => paperEGCCompactifiedCorrection p.1 p.2.1 p.2.2) atTop := by
  apply tendstoUniformly_tsum
    (show Summable (fun q : XiZeroCopy => 8 / ‖xiSpectralPoint q‖^2) from
      by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
  intro q p
  exact norm_paperEGCCircleCopy_le p.1 p.2.1 p.2.2 q

/-- The complete row extends continuously through the projective point. -/
theorem continuous_paperEGCCompactifiedCorrection (eps x : PaperEGCSmallParameter) :
    Continuous (paperEGCCompactifiedCorrection eps x) := by
  apply continuous_tsum (fun q => continuous_paperEGCCircleCopy eps x q)
    (show Summable (fun q : XiZeroCopy => 8 / ‖xiSpectralPoint q‖^2) from
      by simpa only [mul_one_div] using xiSpectralPoint_inv_sq_summable.mul_left 8)
  intro q θ
  exact norm_paperEGCCircleCopy_le eps x θ q

/-- The original complete row is recovered exactly at every finite chart point. -/
theorem paperEGCCompactifiedCorrection_eq_line (eps x : PaperEGCSmallParameter) (θ : ℝ)
    (hc : Real.cos (Real.pi * θ) ≠ 0) :
    paperEGCCompactifiedCorrection eps x θ =
      paperEGCCompleteCorrection eps x (Real.tan (Real.pi * θ)) := by
  unfold paperEGCCompactifiedCorrection paperEGCCompleteCorrection
  exact tsum_congr fun q => paperEGCCircleCopy_eq_line eps x θ q hc

/-- No copy leaves an unrecorded mass at the compactification point. -/
theorem paperEGCCompactifiedCorrection_eq_zero_of_cos_eq_zero
    (eps x : PaperEGCSmallParameter) (θ : ℝ) (hc : Real.cos (Real.pi * θ) = 0) :
    paperEGCCompactifiedCorrection eps x θ = 0 := by
  unfold paperEGCCompactifiedCorrection
  simp only [paperEGCCircleCopy_eq_zero_of_cos_eq_zero eps x θ _ hc, tsum_zero]

theorem paperEGCCompactifiedCorrection_infinity (eps x : PaperEGCSmallParameter) :
    paperEGCCompactifiedCorrection eps x (1 / 2) = 0 := by
  apply paperEGCCompactifiedCorrection_eq_zero_of_cos_eq_zero
  rw [mul_one_div, Real.cos_pi_div_two]

theorem paperEGCCompactifiedCorrection_zero (eps x : PaperEGCSmallParameter) :
    paperEGCCompactifiedCorrection eps x 0 = paperEGCCompleteCorrection eps x 0 := by
  simpa using paperEGCCompactifiedCorrection_eq_line eps x 0 (by simp)

/-- The complete correction descends to a unit circle without changing any finite value. -/
theorem paperEGCCompactifiedCorrection_periodic (eps x : PaperEGCSmallParameter) :
    Function.Periodic (paperEGCCompactifiedCorrection eps x) 1 := by
  intro θ
  exact tsum_congr fun q => paperEGCCircleCopy_periodic eps x q θ

/-- The full compactified profile retains the nonzero centered obstruction. -/
theorem paperEGCCompactifiedCorrection_centered_re_neg (n : ℕ) :
    (paperEGCCompactifiedCorrection (paperEGCScale n) paperEGCZeroOffset 0).re < 0 := by
  rw [paperEGCCompactifiedCorrection_zero]
  exact paperEGCCompleteCorrection_centered_re_neg n

theorem paperEGCCompactifiedCorrection_not_identically_zero (n : ℕ) :
    ¬ ∀ θ : ℝ, paperEGCCompactifiedCorrection (paperEGCScale n) paperEGCZeroOffset θ = 0 := by
  intro h
  have hn := paperEGCCompactifiedCorrection_centered_re_neg n
  rw [h 0, Complex.zero_re] at hn
  exact lt_irrefl 0 hn

end
end RHTower
