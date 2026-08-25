import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneralDualExpansion
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftGeneralPowerBound

/-!
# Derivative identity for the general Gaussian zeta AFE

The exact two-series AFE holds on an open neighbourhood of every point in the
critical strip.  Germ equality therefore passes to complex derivatives with
no extra analytic hypothesis or axiom.
-/

noncomputable section

namespace RHTower

open Complex Filter Set

def smoothAFEZetaGeneralTwoSeries (x : ℝ) (s : ℂ) : ℂ :=
  (∑' n : ℕ, (n + 1 : ℂ) ^ (-s) *
      smoothAFECutoff ((n + 1 : ℝ) / x)) -
    (∑' n : ℕ,
      (zetaChi s * (n + 1 : ℂ) ^ (s - 1)) *
        smoothAFEZetaDualCutoffGeneral s
          (1 / ((n + 1 : ℝ) * x))) -
    smoothAFEZetaShiftedPoleResidue s x

theorem riemannZeta_eventuallyEq_smoothAFEZetaGeneralTwoSeries
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    Filter.EventuallyEq (nhds s) riemannZeta
      (smoothAFEZetaGeneralTwoSeries x) := by
  have hopen0 : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hopen1 : IsOpen {z : ℂ | z.re < 1} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hn0 : {z : ℂ | 0 < z.re} ∈ nhds s := hopen0.mem_nhds h0
  have hn1 : {z : ℂ | z.re < 1} ∈ nhds s := hopen1.mem_nhds h1
  filter_upwards [hn0, hn1] with z hz0 hzlt
  have hzneq : z ≠ 1 := by
    intro hz
    subst z
    norm_num at hzlt
  exact riemannZeta_eq_two_tsum_smoothAFE_general hx hzneq hz0 hzlt

theorem deriv_riemannZeta_eq_deriv_smoothAFEZetaGeneralTwoSeries
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    deriv riemannZeta s = deriv (smoothAFEZetaGeneralTwoSeries x) s :=
  (riemannZeta_eventuallyEq_smoothAFEZetaGeneralTwoSeries hx h0 h1).deriv_eq

theorem deriv_riemannZeta_displaced_eq_deriv_smoothAFEZetaGeneralTwoSeries
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) :
    deriv riemannZeta (displacedLinePt d τ) =
      deriv (smoothAFEZetaGeneralTwoSeries x) (displacedLinePt d τ) := by
  apply deriv_riemannZeta_eq_deriv_smoothAFEZetaGeneralTwoSeries hx
  · exact (displacedLinePt_mem_openStrip hd hdhalf τ).1
  · exact (displacedLinePt_mem_openStrip hd hdhalf τ).2

theorem hasDerivAt_riemannZeta_displaced_eq_smoothAFEZetaGeneralTwoSeries
    {x d : ℝ} (hx : 0 < x) (hd : 0 < d) (hdhalf : d < 1 / 2)
    (τ : ℝ) :
    HasDerivAt (fun u : ℝ => riemannZeta (displacedLinePt d u))
      (deriv (smoothAFEZetaGeneralTwoSeries x) (displacedLinePt d τ) * I) τ := by
  have hsneq : displacedLinePt d τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    rw [displacedLinePt_re] at hre
    norm_num at hre
    linarith
  have hline : HasDerivAt (displacedLinePt d) I τ := by
    have hu : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 τ :=
      (hasDerivAt_id τ).ofReal_comp
    have h := (hu.mul_const I).const_add (((1 / 2 - d : ℝ) : ℂ))
    have h' : HasDerivAt (fun u : ℝ =>
        (((1 / 2 - d : ℝ) : ℂ) + (u : ℂ) * I)) I τ := by
      simpa only [one_mul] using h
    exact h'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => rfl)
  have h := (differentiableAt_riemannZeta hsneq).hasDerivAt.comp
    τ hline
  rw [deriv_riemannZeta_displaced_eq_deriv_smoothAFEZetaGeneralTwoSeries
    hx hd hdhalf τ] at h
  exact h

end RHTower
