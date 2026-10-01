import GaloisForLFunctions.RHTower.ChiLogDerivHigherDerivatives
import Mathlib.Analysis.Calculus.MeanValue

open Complex Set
noncomputable section
namespace RHTower

/-- The actual chi logarithmic derivative is differentiable off the real axis. -/
theorem differentiableAt_logDeriv_zetaChi {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (logDeriv zetaChi) z := by
  have hc : DifferentiableAt ℂ chiLogDerivClosed z := by
    unfold chiLogDerivClosed
    exact ((((analyticAt_halfDigamma hz).differentiableAt.div_const 2).neg.sub
      ((analyticAt_digamma_reflectHalf hz).differentiableAt.div_const 2)).add_const _)
  exact hc.congr_of_eventuallyEq (logDeriv_zetaChi_eventuallyEq hz)

/-- The logarithmic slopes of actual chi factors at a compact strip shift and
at the critical line differ by a conductor-scale quantity. -/
theorem norm_logDeriv_zetaChi_compact_shift_le {s : ℂ} {tau : ℝ}
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1) (htau : 4 ≤ tau) (him : 2 * |s.im| ≤ tau) :
    ‖logDeriv zetaChi (s + (tau : ℂ) * I) - logDeriv zetaChi (linePt tau)‖ ≤
      (10 / tau) * ‖s - (1 / 2 : ℂ)‖ := by
  let z0 := linePt tau
  let z1 := s + (tau : ℂ) * I
  have htau0 : 0 < tau := by linarith
  have hgeom : ∀ z ∈ segment ℝ z0 z1, 0 ≤ z.re ∧ z.re ≤ 1 ∧ tau / 2 ≤ z.im := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    have hre : (AffineMap.lineMap z0 z1 r).re = (1 - r) / 2 + r * s.re := by
      simp [z0, z1, linePt, AffineMap.lineMap_apply]
      ring
    have hi : (AffineMap.lineMap z0 z1 r).im = tau + r * s.im := by
      simp [z0, z1, linePt, AffineMap.lineMap_apply]
      ring
    rw [hre, hi]
    have hr0 := hr.1
    have hr1 := hr.2
    have hmul0 := mul_nonneg hr0 hs0
    have hmul1 := mul_nonneg hr0 (sub_nonneg.mpr hs1)
    have hsim := neg_abs_le s.im
    have hprod := mul_nonneg hr0 (by linarith : 0 ≤ s.im + |s.im|)
    have hprod' := mul_nonneg (sub_nonneg.mpr hr1) (abs_nonneg s.im)
    constructor
    · nlinarith
    constructor <;> nlinarith
  have hdiff : ∀ z ∈ segment ℝ z0 z1, DifferentiableAt ℂ (logDeriv zetaChi) z := by
    intro z hz
    apply differentiableAt_logDeriv_zetaChi
    have hg := (hgeom z hz).2.2
    linarith
  have hbound : ∀ z ∈ segment ℝ z0 z1, ‖deriv (logDeriv zetaChi) z‖ ≤ 10 / tau := by
    intro z hz
    obtain ⟨hz0, hz1, hzim⟩ := hgeom z hz
    have hzpos : 0 < z.im := by linarith
    have h := norm_iteratedDeriv_logDeriv_zetaChi_le (n := 1) (by omega)
      (by linarith : -2 < z.re) (by linarith : z.re < 3)
      (by rw [abs_of_pos hzpos]; linarith : 2 ≤ |z.im|)
    have hh : ‖deriv (logDeriv zetaChi) z‖ ≤ 5 / z.im := by
      simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, mul_one, pow_one,
        abs_of_pos hzpos] using h
    have hfrac : 5 / z.im ≤ 10 / tau := by
      apply (div_le_div_iff₀ hzpos htau0).mpr
      linarith
    exact hh.trans hfrac
  have hmvt := (convex_segment z0 z1).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (left_mem_segment ℝ z0 z1) (right_mem_segment ℝ z0 z1)
  have hsub : z1 - z0 = s - (1 / 2 : ℂ) := by
    dsimp only [z0, z1, linePt]
    push_cast
    ring
  rw [hsub] at hmvt
  exact hmvt

end RHTower
