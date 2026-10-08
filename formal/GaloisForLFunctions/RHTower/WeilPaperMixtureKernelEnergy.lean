import GaloisForLFunctions.RHTower.WeilPaperRealificationEnergy

/-!
# Full energy depends only on the mixture autocorrelation

Every finite native mixture has an admissible aggregate kernel, including signed
mixtures. Its full energy is exactly the pole-plus-gamma functional of that kernel.
-/

open Complex MeasureTheory Zeta23
open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided WeilSpectral

/-- The entire autocorrelation kernel is a finite sum of admissible kernels. -/
theorem mixtureSample_eq_kernel_sum (c : WeilTestFn →₀ ℝ) :
    mixtureSample c = ∑ f ∈ c.support, (c f : ℂ) • EF.weilTest f.1 f.1 := by
  funext y
  simp only [mixtureSample, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

theorem admissible_mixtureSample (c : WeilTestFn →₀ ℝ) :
    Admissible (mixtureSample c) := by
  rw [mixtureSample_eq_kernel_sum]
  exact Admissible.sum c.support fun f _ => (admissible_weilTest f.2.1 f.2.2).smul _

/-- No information outside the aggregate autocorrelation can affect full energy. -/
theorem energy_eq_weilArchRe_mixtureSample (c : WeilTestFn →₀ ℝ) :
    energy c = weilArchRe (mixtureSample c) := by
  rw [mixtureSample_eq_kernel_sum, weilArchRe_eq,
    weilFullFunctional_sum 0 c.support
      (fun f _ => (admissible_weilTest f.2.1 f.2.2).smul (c f : ℂ))]
  simp only [weilFullFunctional_smul, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    energy, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, weilArchRe_eq]

/-- Equal mixture autocorrelations have equal full energies. -/
theorem energy_eq_of_mixtureSample_eq (c d : WeilTestFn →₀ ℝ)
    (h : mixtureSample c = mixtureSample d) : energy c = energy d := by
  rw [energy_eq_weilArchRe_mixtureSample, h, ← energy_eq_weilArchRe_mixtureSample]

end RHTower.WeilWorkPBAP
