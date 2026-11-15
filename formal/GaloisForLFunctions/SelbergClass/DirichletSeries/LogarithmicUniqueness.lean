import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Uniqueness of logarithmic Dirichlet coefficients

Equality of exponentiated absolutely convergent Dirichlet series determines
all coefficients at indices greater than one. Differentiation removes the
constant logarithm branch, and Dirichlet-series uniqueness recovers each coefficient.
-/

noncomputable section
open Complex Filter Topology Set

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

/-- Equality after exponentiation determines all nonconstant Dirichlet coefficients.
Differentiation removes the additive logarithm branch. -/
theorem coeff_eq_of_exp_lSeries_eq {f g : ℕ → ℂ} {B : ℝ}
    (hf : ∀ s : ℂ, B < s.re → LSeriesSummable f s)
    (hg : ∀ s : ℂ, B < s.re → LSeriesSummable g s)
    (he : ∀ s : ℂ, B < s.re → Complex.exp (LSeries f s) = Complex.exp (LSeries g s))
    {n : ℕ} (hn : 1 < n) : f n = g n := by
  have hfa : LSeries.abscissaOfAbsConv f ≤ (B + 1 : ℝ) := by
    simpa only [Complex.ofReal_re] using
      (hf ((B + 1 : ℝ) : ℂ) (by simp only [Complex.ofReal_re]; linarith)).abscissaOfAbsConv_le
  have hga : LSeries.abscissaOfAbsConv g ≤ (B + 1 : ℝ) := by
    simpa only [Complex.ofReal_re] using
      (hg ((B + 1 : ℝ) : ℂ) (by simp only [Complex.ofReal_re]; linarith)).abscissaOfAbsConv_le
  have hfbs {s : ℂ} (hs : B + 1 < s.re) : LSeries.abscissaOfAbsConv f < s.re :=
    hfa.trans_lt (by exact_mod_cast hs)
  have hgbs {s : ℂ} (hs : B + 1 < s.re) : LSeries.abscissaOfAbsConv g < s.re :=
    hga.trans_lt (by exact_mod_cast hs)
  have hderiv {s : ℂ} (hs : B + 1 < s.re) :
      LSeries (LSeries.logMul f) s = LSeries (LSeries.logMul g) s := by
    have hdf := (LSeries_hasDerivAt (hfbs hs)).cexp
    have hdg := (LSeries_hasDerivAt (hgbs hs)).cexp
    have hloc : (fun z : ℂ => Complex.exp (LSeries f z)) =ᶠ[𝓝 s]
        (fun z : ℂ => Complex.exp (LSeries g z)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by linarith : B < s.re)] with z hz
      exact he z hz
    have h := (hdf.congr_of_eventuallyEq hloc.symm).deriv.symm.trans hdg.deriv
    rw [he s (by linarith)] at h
    have hcancel := mul_left_cancel₀ (Complex.exp_ne_zero (LSeries g s)) h
    exact neg_injective hcancel
  have hlogf := LSeriesSummable_logMul_of_lt_re (hfbs (s := (B + 2 : ℝ)) (by simp))
  have hlogg := LSeriesSummable_logMul_of_lt_re (hgbs (s := (B + 2 : ℝ)) (by simp))
  have hc : LSeries.logMul f n = LSeries.logMul g n := by
    apply LSeries.eq_of_LSeries_eventually_eq
      (hlogf.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
      (hlogg.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    · filter_upwards [eventually_gt_atTop (B + 1)] with x hx
      exact hderiv (s := (x : ℂ)) hx
    · omega
  change Complex.log (n : ℂ) * f n = Complex.log (n : ℂ) * g n at hc
  apply mul_left_cancel₀ _ hc
  rw [← Complex.natCast_log]
  exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hn)).ne'

end GaloisForLFunctions.SelbergClass.DirichletSeries
