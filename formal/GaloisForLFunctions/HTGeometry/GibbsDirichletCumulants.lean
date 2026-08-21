import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Gibbs cumulants of a Dirichlet partition

For a Dirichlet series `Z(s) = ∑ f n · n^{-s}` the logarithmic derivative is minus the Gibbs
expectation of `log n` under the weights `f n · n^{-s}/Z(s)`, and the derivative of the logarithmic
derivative is the Gibbs variance of `log n`.  These are the two cumulant identities that turn a
formation-work derivative into a spectral moment.
-/

open LSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Gibbs expectation of `log n` for a Dirichlet partition. -/
def gibbsLogMean (f : ℕ → ℂ) (s : ℂ) : ℂ := LSeries (logMul f) s / LSeries f s

/-- Gibbs second moment of `log n` for a Dirichlet partition. -/
def gibbsLogSecondMoment (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  LSeries (logMul (logMul f)) s / LSeries f s

/-- Gibbs variance of `log n` for a Dirichlet partition. -/
def gibbsLogVar (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  gibbsLogSecondMoment f s - gibbsLogMean f s ^ 2

/-- **First cumulant.**  The logarithmic derivative of a Dirichlet partition is minus the Gibbs
expectation of `log n`. -/
theorem logDeriv_LSeries {f : ℕ → ℂ} {s : ℂ} (habs : abscissaOfAbsConv f < s.re) :
    logDeriv (LSeries f) s = -gibbsLogMean f s := by
  rw [logDeriv_apply, LSeries_deriv habs, gibbsLogMean, neg_div]

theorem isOpen_absConv (f : ℕ → ℂ) :
    IsOpen {z : ℂ | abscissaOfAbsConv f < (z.re : EReal)} := by
  have hcont : Continuous fun z : ℂ => ((z.re : ℝ) : EReal) :=
    continuous_coe_real_ereal.comp Complex.continuous_re
  exact hcont.isOpen_preimage _ isOpen_Ioi

/-- The derivative of a Dirichlet partition, as an eventual identity. -/
theorem deriv_LSeries_eventuallyEq {f : ℕ → ℂ} {s : ℂ} (habs : abscissaOfAbsConv f < s.re) :
    deriv (LSeries f) =ᶠ[nhds s] fun z => -LSeries (logMul f) z := by
  filter_upwards [(isOpen_absConv f).mem_nhds habs] with z hz
  exact LSeries_deriv hz

/-- **Second cumulant.**  The derivative of the logarithmic derivative of a Dirichlet partition is
the Gibbs variance of `log n`. -/
theorem hasDerivAt_logDeriv_LSeries {f : ℕ → ℂ} {s : ℂ} (habs : abscissaOfAbsConv f < s.re)
    (hne : LSeries f s ≠ 0) :
    HasDerivAt (logDeriv (LSeries f)) (gibbsLogVar f s) s := by
  have habs2 : abscissaOfAbsConv (logMul f) < (s.re : EReal) := by
    rwa [abscissaOfAbsConv_logMul]
  have hZ : HasDerivAt (LSeries f) (-LSeries (logMul f) s) s := LSeries_hasDerivAt habs
  have hZ' : HasDerivAt (deriv (LSeries f)) (LSeries (logMul (logMul f)) s) s := by
    have h1 : HasDerivAt (fun z => -LSeries (logMul f) z)
        (-(-LSeries (logMul (logMul f)) s)) s := (LSeries_hasDerivAt habs2).neg
    rw [neg_neg] at h1
    exact h1.congr_of_eventuallyEq (deriv_LSeries_eventuallyEq habs)
  have hdiv := hZ'.div hZ hne
  refine hdiv.congr_deriv ?_
  have hval : deriv (LSeries f) s = -LSeries (logMul f) s := LSeries_deriv habs
  rw [hval, gibbsLogVar, gibbsLogSecondMoment, gibbsLogMean]
  field_simp


theorem gibbsLogMean_eventuallyEq {f : ℕ → ℂ} {s : ℂ} (habs : abscissaOfAbsConv f < s.re) :
    gibbsLogMean f =ᶠ[nhds s] fun z => -logDeriv (LSeries f) z := by
  filter_upwards [(isOpen_absConv f).mem_nhds habs] with z hz
  rw [logDeriv_LSeries hz, neg_neg]

/-- **The Gibbs first moment moves by the variance.** -/
theorem hasDerivAt_gibbsLogMean {f : ℕ → ℂ} {s : ℂ} (habs : abscissaOfAbsConv f < s.re)
    (hne : LSeries f s ≠ 0) :
    HasDerivAt (gibbsLogMean f) (-gibbsLogVar f s) s := by
  have h := (hasDerivAt_logDeriv_LSeries habs hne).neg
  exact h.congr_of_eventuallyEq (gibbsLogMean_eventuallyEq habs)

end

end GaloisForLFunctions.HTGeometry
