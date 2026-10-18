import GaloisForLFunctions.BiScaleUncertainty.CompactFiniteJumpWeilFormula

/-! The full half-line polar integral of a compact continuous autocorrelation
is the product of the source's two exponential moments. No source derivatives
or vanishing moment assumptions are needed. -/

open Complex MeasureTheory Set Filter
open scoped CompactlySupported ComplexConjugate
open Zeta23
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
noncomputable section
set_option autoImplicit false

theorem integral_polar_autocorr_eq_moments (f : C_c(ℝ, ℝ)) :
    (∫ x in Ici (0 : ℝ), polarDensity x*autocorr f x) =
      (∫ u, Real.exp (u/2)*f u)*(∫ u, Real.exp (-(u/2))*f u) := by
  let F : ℝ → ℂ := fun u => (f u : ℂ)
  have hFc : Continuous F := Complex.continuous_ofReal.comp f.continuous
  have hFs : HasCompactSupport F := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hw : EF.weilTest F F = fun x => (autocorr f x : ℂ) := by
    funext x
    simpa only [F, neg_neg, autocorr_neg] using (autocorr_eq_weilTest f (-x)).symm
  have ht := EF.paperFT_weilTest hFc hFc hFs hFs (I/2)
  rw [hw, WeilLevyPole.paperFT_ofReal_I_div_two,
    show (starRingEnd ℂ) (I/2) = -I/2 by rw [map_div₀, Complex.conj_I, map_ofNat],
    WeilLevyPole.paperFT_ofReal_I_div_two, WeilLevyPole.paperFT_ofReal_neg_I_div_two,
    Complex.conj_ofReal] at ht
  have hm : (∫ x, autocorr f x*Real.exp (-x/2)) =
      (∫ u, Real.exp (u/2)*f u)*(∫ u, Real.exp (-(u/2))*f u) := by
    simpa only [← Complex.ofReal_mul, Complex.ofReal_re, neg_div, mul_comm] using congrArg Complex.re ht
  have hp : (∫ x, autocorr f x*Real.exp (x/2)) =
      (∫ u, Real.exp (u/2)*f u)*(∫ u, Real.exp (-(u/2))*f u) := by
    rw [← integral_neg_eq_self (fun x => autocorr f x*Real.exp (x/2))]
    simpa only [autocorr_neg] using hm
  have hc := continuous_autocorr_compact f
  have hs := hasCompactSupport_autocorr f.hasCompactSupport
  have hip : Integrable (fun x => autocorr f x*Real.exp (x/2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  have him : Integrable (fun x => autocorr f x*Real.exp (-x/2)) :=
    (hc.mul (by fun_prop)).integrable_of_hasCompactSupport hs.mul_right
  have hcosh : (∫ x, autocorr f x*Real.cosh (x/2)) =
      (∫ u, Real.exp (u/2)*f u)*(∫ u, Real.exp (-(u/2))*f u) := by
    have he : (fun x => autocorr f x*Real.cosh (x/2)) =
        fun x => (autocorr f x*Real.exp (x/2)+autocorr f x*Real.exp (-x/2))/2 := by
      funext x
      rw [Real.cosh_eq]
      simp only [neg_div]
      ring
    rw [he, integral_div, integral_add hip him, hp, hm]
    ring
  have heven : (fun x => autocorr f |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr f x*Real.cosh (x/2) := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · simp only [abs_of_nonpos hx, neg_div, Real.cosh_neg, autocorr_neg]
  have hh := integral_comp_abs (f := fun x => autocorr f x*Real.cosh (x/2))
  rw [heven] at hh
  have he : (fun x => polarDensity x*autocorr f x) =
      fun x => 2*(autocorr f x*Real.cosh (x/2)) := by
    funext x
    unfold polarDensity
    ring
  rw [he, integral_const_mul, integral_Ici_eq_integral_Ioi, ← hh, hcosh]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
