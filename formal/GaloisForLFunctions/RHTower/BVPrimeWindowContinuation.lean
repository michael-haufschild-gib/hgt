import GaloisForLFunctions.RHTower.BVPrimeWindowDirichlet
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowContinuation

/-!
# Canonical continuation of bounded-variation prime windows

This file pole-fills the zeta pole in the Dirichlet identity for an arbitrary compactly supported
complex BV window.  The construction is concrete: its only non-entire factor is the logarithmic
derivative of the pole-filled zeta, so the remaining divisor is exactly the zeta-zero divisor
modulo Mellin cancellation.
-/

open Complex Filter Function Set

noncomputable section

namespace RHTower
namespace CompactBVPrimeWindow

/-- Entire numerator whose zero at `3/2` encodes cancellation of the shifted zeta pole. -/
def poleNumerator (W : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  2 * W.mellinTransform (3 / 2) * regularizedRiemannZeta (s - 1 / 2) -
    2 * W.mellinTransform s

/-- The pole-filled main part of the BV prime source. -/
def poleFilledMain (W : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  dslope W.poleNumerator (3 / 2) s +
    2 * W.mellinTransform s *
      logDeriv regularizedRiemannZeta (s - 1 / 2)

/-- Canonical continuation of the polar-renormalized BV prime-window source. -/
def continuedSource (W : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  W.poleFilledMain s - 2 * W.errorSeries s

theorem differentiable_poleNumerator (W : CompactBVPrimeWindow) :
    Differentiable ℂ W.poleNumerator := by
  unfold poleNumerator
  exact ((differentiable_regularizedRiemannZeta.comp
      (differentiable_id.sub_const (1 / 2))).const_mul
        (2 * W.mellinTransform (3 / 2))).sub
    (W.differentiable_mellinTransform.const_mul 2)

@[simp] theorem poleNumerator_three_halves (W : CompactBVPrimeWindow) :
    W.poleNumerator (3 / 2) = 0 := by
  rw [poleNumerator]
  norm_num [regularizedRiemannZeta_one]

/-- The divided-difference numerator is entire at the cancelled zeta pole. -/
theorem differentiable_poleDividedDifference (W : CompactBVPrimeWindow) :
    Differentiable ℂ (dslope W.poleNumerator (3 / 2)) := by
  rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
  exact W.differentiable_poleNumerator.differentiableOn

/-- The completed BV source is meromorphic on the full quadrature half-plane. -/
theorem meromorphicOn_continuedSource_rightHalf (W : CompactBVPrimeWindow) :
    MeromorphicOn W.continuedSource {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ (dslope W.poleNumerator (3 / 2)) s :=
    (W.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ W.mellinTransform s :=
    (W.differentiable_mellinTransform.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hlog : MeromorphicAt
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s :=
    MeromorphicAt.comp_analyticAt
      (meromorphicAt_logDeriv_regularizedRiemannZeta (s - 1 / 2)) hshift
  have herr : AnalyticAt ℂ W.errorSeries s :=
    (W.differentiableOn_errorSeries_rightHalf.analyticOnNhd hUopen) s hs
  exact (hdiv.meromorphicAt.add
    ((analyticAt_const.mul hM).meromorphicAt.mul hlog)).sub
      (analyticAt_const.mul herr).meromorphicAt

/-- Away from a zero of the pole-filled zeta, the canonical BV source is analytic. -/
theorem analyticAt_continuedSource_of_regularizedZeta_ne_zero
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 1 / 2 < s.re)
    (hz : regularizedRiemannZeta (s - 1 / 2) ≠ 0) :
    AnalyticAt ℂ W.continuedSource s := by
  let U : Set ℂ := {z : ℂ | 1 / 2 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hdiv : AnalyticAt ℂ (dslope W.poleNumerator (3 / 2)) s :=
    (W.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hM : AnalyticAt ℂ W.mellinTransform s :=
    (W.differentiable_mellinTransform.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hreg : AnalyticAt ℂ regularizedRiemannZeta (s - 1 / 2) :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) (s - 1 / 2) (Set.mem_univ _)
  have hlog : AnalyticAt ℂ
      (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) s := by
    rw [show (fun z : ℂ => logDeriv regularizedRiemannZeta (z - 1 / 2)) =
        fun z : ℂ => deriv regularizedRiemannZeta (z - 1 / 2) /
          regularizedRiemannZeta (z - 1 / 2) by
      funext z
      rw [logDeriv_apply]]
    have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
    have hnum := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg.deriv hshift
    have hden := AnalyticAt.comp (f := fun z : ℂ => z - 1 / 2) (x := s)
      hreg hshift
    simpa only [Function.comp_apply] using! hnum.div hden hz
  have herr : AnalyticAt ℂ W.errorSeries s :=
    (W.differentiableOn_errorSeries_rightHalf.analyticOnNhd hUopen) s hs
  exact (hdiv.add ((analyticAt_const.mul hM).mul hlog)).sub
    (analyticAt_const.mul herr)

/-- The shifted zeta pole at `3/2` is removed for every BV window. -/
theorem analyticAt_continuedSource_three_halves (W : CompactBVPrimeWindow) :
    AnalyticAt ℂ W.continuedSource (3 / 2) := by
  apply W.analyticAt_continuedSource_of_regularizedZeta_ne_zero
  · norm_num
  · norm_num [regularizedRiemannZeta_one]

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- On the absolute-convergence half-plane, the pole-filled expression is the polar zeta term plus
the Mellin-weighted von-Mangoldt logarithmic derivative. -/
theorem poleFilledMain_eq_zetaLogDeriv
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    W.poleFilledMain s =
      2 * W.mellinTransform (3 / 2) * riemannZeta (s - 1 / 2) +
        2 * W.mellinTransform s * zetaLogDeriv (s - 1 / 2) := by
  have ht : s - 1 / 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re] at hre
    linarith
  have hz : riemannZeta (s - 1 / 2) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      norm_num [Complex.sub_re]
      linarith)
  have hs0 : s ≠ 3 / 2 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [poleFilledMain, dslope_of_ne _ hs0, slope_def_field,
    W.poleNumerator_three_halves, sub_zero, poleNumerator,
    regularizedRiemannZeta_of_ne_one ht,
    logDeriv_regularizedRiemannZeta_eq ht hz]
  have hden : (s - 1 / 2) - 1 = s - 3 / 2 := by ring
  rw [hden]
  have hden0 : s - 3 / 2 ≠ 0 := sub_ne_zero.mpr hs0
  let d : ℂ := s - 3 / 2
  have hd : d ≠ 0 := by simpa only [d] using hden0
  let A : ℂ := W.mellinTransform (3 / 2)
  let B : ℂ := W.mellinTransform s
  let Z : ℂ := riemannZeta (s - 1 / 2)
  let D : ℂ := zetaLogDeriv (s - 1 / 2)
  rw [show s - 3 / 2 = d by rfl]
  change (2 * A * (d * Z) - 2 * B) / d +
      2 * B * (1 / d + D) = 2 * A * Z + 2 * B * D
  rw [div_eq_mul_inv, one_div]
  have hc : d * d⁻¹ = 1 := mul_inv_cancel₀ hd
  calc
    (2 * A * (d * Z) - 2 * B) * d⁻¹ +
        2 * B * (d⁻¹ + D) =
      2 * A * Z * (d * d⁻¹) + 2 * B * D := by ring
    _ = 2 * A * Z + 2 * B * D := by rw [hc]; ring

/-- Far right, the continuation is the exact polar-zeta/log-derivative expression minus the
holomorphic BV quadrature remainder. -/
theorem continuedSource_eq_zetaLogDeriv
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    W.continuedSource s =
      2 * W.mellinTransform (3 / 2) * riemannZeta (s - 1 / 2) +
        2 * W.mellinTransform s * zetaLogDeriv (s - 1 / 2) -
          2 * W.errorSeries s := by
  rw [continuedSource, W.poleFilledMain_eq_zetaLogDeriv hs]

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- The honest moving-window coefficient has an absolutely convergent L-series initially. -/
theorem weightedPrimeWindow_LSeriesSummable
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable W.weightedPrimeWindow s := by
  have hdouble : Summable (W.doubleTerm s) := W.summable_doubleTerm hs
  have hswap : Summable (fun nk : ℕ × ℕ => W.doubleTerm s (nk.2, nk.1)) := by
    simpa only [Function.comp_apply, Equiv.prodComm_apply] using!
      hdouble.comp_injective (Equiv.prodComm ℕ ℕ).injective
  have houter : Summable
      (fun n : ℕ => ∑' k : ℕ, W.doubleTerm s (k, n)) := hswap.prod
  exact houter.congr fun n => W.tsum_doubleTerm_left s n

/-- The concrete prime-polar coefficient attached to a BV window. -/
def polarCoefficient (W : CompactBVPrimeWindow) (n : ℕ) : ℂ :=
  2 * W.mellinTransform (3 / 2) * Real.sqrt n -
    2 * W.weightedPrimeWindow n

/-- The prime-polar coefficient has an absolutely convergent L-series on its initial half-plane. -/
theorem polarCoefficient_LSeriesSummable
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable W.polarCoefficient s := by
  have hsqrt := sqrt_LSeriesSummable hs
  have hwindow := W.weightedPrimeWindow_LSeriesSummable hs
  have hdiff := (hsqrt.smul (2 * W.mellinTransform (3 / 2))).sub
    (hwindow.smul 2)
  change Summable (LSeries.term W.polarCoefficient s)
  change Summable (LSeries.term _ s) at hdiff
  exact hdiff.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, polarCoefficient]

/-- The ordinary Dirichlet series of the exact finite prime-polar coefficient equals the canonical
continued source on `Re s > 3/2`. -/
theorem LSeries_polarCoefficient_eq_continuedSource
    (W : CompactBVPrimeWindow) {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeries W.polarCoefficient s = W.continuedSource s := by
  have hsqrt := sqrt_LSeriesSummable hs
  have hwindow := W.weightedPrimeWindow_LSeriesSummable hs
  have hscaledSqrt := hsqrt.smul (2 * W.mellinTransform (3 / 2))
  have hscaledWindow := hwindow.smul (2 : ℂ)
  calc
    LSeries W.polarCoefficient s =
        LSeries
          ((2 * W.mellinTransform (3 / 2)) •
              (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) -
            (2 : ℂ) • W.weightedPrimeWindow) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, polarCoefficient]
    _ = (2 * W.mellinTransform (3 / 2)) *
          LSeries (fun n : ℕ => ((Real.sqrt n : ℝ) : ℂ)) s -
        2 * LSeries W.weightedPrimeWindow s := by
      rw [LSeries_sub hscaledSqrt hscaledWindow, LSeries_smul, LSeries_smul]
    _ = (2 * W.mellinTransform (3 / 2)) * riemannZeta (s - 1 / 2) -
        2 * (-W.mellinTransform s * zetaLogDeriv (s - 1 / 2) +
          W.errorSeries s) := by
      rw [LSeries_sqrt_eq_riemannZeta_shift hs,
        W.LSeries_weightedPrimeWindow_eq_zetaLogDeriv hs]
    _ = 2 * W.mellinTransform (3 / 2) * riemannZeta (s - 1 / 2) +
        2 * W.mellinTransform s * zetaLogDeriv (s - 1 / 2) -
          2 * W.errorSeries s := by ring
    _ = W.continuedSource s := (W.continuedSource_eq_zetaLogDeriv hs).symm

end CompactBVPrimeWindow
end RHTower
