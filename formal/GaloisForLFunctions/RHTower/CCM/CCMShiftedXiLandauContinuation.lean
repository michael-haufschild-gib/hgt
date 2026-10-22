import GaloisForLFunctions.RHTower.CCM.CCMShiftedXiNormalConvergence
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Landau continuation of the rectangular shifted-zeta carrier

An eventual lower bound makes the tail coefficientwise nonnegative.  The
scale-local Landau theorem then places its absolute-convergence boundary to
the left of the rightmost Xi displacement.  This module turns the resulting
L-series into an analytic continuation of the shifted-zeta carrier and uses
the Xi-cancelled normal sum to cross all shifted poles simultaneously.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- The analytic shifted-zeta continuation reconstructed from the Landau
tail L-series. -/
def xiRectangularLandauAnalyticShiftedSeries
    (L C : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  (LSeries
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ)) s -
    C * riemannZeta s + xiRectangularLandauPrefixSeries L C N s) / 2

/-- Once the nonnegative tail converges at a real point `sigma > 1`, its
reconstructed shifted-zeta continuation is holomorphic on `Re s > sigma`. -/
theorem differentiableOn_xiRectangularLandauAnalyticShiftedSeries
    (L C : ℝ) (N : ℕ) {sigma : ℝ} (hsigma : 1 < sigma)
    (hsum : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ))
      (sigma : ℂ)) :
    DifferentiableOn ℂ (xiRectangularLandauAnalyticShiftedSeries L C N)
      {s : ℂ | sigma < s.re} := by
  intro s hs
  change sigma < s.re at hs
  have habs := hsum.abscissaOfAbsConv_le
  have habslt : LSeries.abscissaOfAbsConv
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ)) < s.re := by
    exact lt_of_le_of_lt habs (by exact_mod_cast hs)
  have hL := (LSeries_hasDerivAt habslt).differentiableAt
  have hsone : s ≠ 1 := by
    intro heq
    subst s
    simp only [Complex.one_re] at hs
    linarith
  have hzeta := differentiableAt_riemannZeta hsone
  have hprefix := differentiable_xiRectangularLandauPrefixSeries L C N s
  simpa only [xiRectangularLandauAnalyticShiftedSeries] using!
    (((hL.sub (hzeta.const_mul (C : ℂ))).add hprefix).div_const (2 : ℂ)).differentiableWithinAt

/-- On the original right half-plane, the reconstructed analytic carrier is
the raw rectangular shifted-zeta series. -/
theorem xiRectangularLandauAnalyticShiftedSeries_eq_shiftedZeta
    (L C : ℝ) (N : ℕ) {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    xiRectangularLandauAnalyticShiftedSeries L C N s =
      xiRectangularShiftedZetaSeries L s := by
  have hL := LSeries_xiRectangularLandauCoefficient_eq_continuation
    L C N hdelta0 hupper hs
  rw [xiRectangularLandauAnalyticShiftedSeries]
  rw [hL]
  rw [xiRectangularLandauContinuation]
  ring

/-- The Xi-cancelled normal carrier and the Xi multiple of the Landau
continuation agree throughout the connected half-plane `Re s > sigma`. -/
theorem xiRectangularCancelledSeries_eq_xi_mul_landauContinuation
    (L C : ℝ) (N : ℕ) {delta sigma : ℝ}
    (hsigma : 1 < sigma) (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy, (xiRightCenteredZero q).re ≤ delta)
    (hsum : LSeriesSummable
      (fun n => ((xiRectangularLandauCoefficient L C N n : ℝ) : ℂ))
      (sigma : ℂ)) :
    Set.EqOn (xiRectangularCancelledSeries L)
      (fun s => xi (s - 1 / 2) *
        xiRectangularLandauAnalyticShiftedSeries L C N s)
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt sigma).isPreconnected
  have hcancelDiff : DifferentiableOn ℂ (xiRectangularCancelledSeries L) U :=
    (differentiableOn_xiRectangularCancelledSeries_rightOne L).mono (by
      intro s hs
      change sigma < s.re at hs
      change 1 < s.re
      linarith)
  have hlandauDiff := differentiableOn_xiRectangularLandauAnalyticShiftedSeries
    L C N hsigma hsum
  have hprodDiff : DifferentiableOn ℂ
      (fun s => xi (s - 1 / 2) *
        xiRectangularLandauAnalyticShiftedSeries L C N s) U := by
    intro s hs
    exact ((xi_differentiable (s - 1 / 2)).comp s
      (differentiableAt_id.sub_const (1 / 2))).differentiableWithinAt.mul
        (hlandauDiff s hs)
  let x0 : ℝ := max sigma (1 + delta) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change sigma < x0
    dsimp only [x0]
    linarith [le_max_left sigma (1 + delta)]
  have hz0right : 1 + delta < z0.re := by
    change 1 + delta < x0
    dsimp only [x0]
    linarith [le_max_right sigma (1 + delta)]
  have hrightOpen : IsOpen {s : ℂ | 1 + delta < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hevent : xiRectangularCancelledSeries L =ᶠ[nhds z0]
      fun s => xi (s - 1 / 2) *
        xiRectangularLandauAnalyticShiftedSeries L C N s := by
    filter_upwards [hrightOpen.mem_nhds hz0right] with s hsright
    rw [xiRectangularCancelledSeries_eq_xi_mul_shiftedZeta
      L hupper hsright,
      xiRectangularLandauAnalyticShiftedSeries_eq_shiftedZeta
        L C N hdelta0 hupper hsright]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hcancelDiff.analyticOnNhd hUopen)
    (hprodDiff.analyticOnNhd hUopen) hUpre hz0U hevent

end

end RHTower
