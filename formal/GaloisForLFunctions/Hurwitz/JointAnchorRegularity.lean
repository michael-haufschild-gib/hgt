import GaloisForLFunctions.Hurwitz.JointAnchorContinuity
import GaloisForLFunctions.HTGeometry.NormalSeriesStrictFDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Joint complex regularity of the actual Hurwitz source

Compact normal convergence of the zero-degree remainder supplies continuous
complex differentiability in the exponent and shift together. This is the
regularity input for the local Hurwitz zero graph through an anchor zero.
-/

open Complex Filter Metric Set
open scoped Topology

namespace HurwitzZetaContinuation

/-- The elementary remainder is jointly analytic wherever the shift has positive real part. -/
theorem analyticAt_remainder_zero_joint (n : ℕ) {p : ℂ × ℂ} (hp : 0 < p.2.re) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => remainder 0 q.1 q.2 n) p := by
  have hna : (n : ℂ) + p.2 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have hn1 : ((n + 1 : ℕ) : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.natCast_re]
    positivity
  simpa only [remainder, taylorPoly_zero, Pi.add_apply, Pi.neg_apply] using
    (((analyticAt_const.add analyticAt_snd).cpow analyticAt_fst.neg hna).fun_sub
      (analyticAt_const.cpow analyticAt_fst.neg hn1))

/-- The actual remainder sum has a continuous complex Fréchet derivative near the anchor. -/
theorem contDiffAt_one_tsum_remainder_zero {s a : ℂ} (hs : 0 < s.re)
    (ha : ‖a - 1‖ < (1 / 2 : ℝ)) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => ∑' n, remainder 0 p.1 p.2 n) (s, a) := by
  let r : ℝ := min (s.re / 4) (((1 / 2 : ℝ) - ‖a - 1‖) / 2)
  have hr : 0 < r := lt_min (by positivity) (by linarith)
  have hrs : 2 * r ≤ s.re / 2 := by
    have := min_le_left (s.re / 4) (((1 / 2 : ℝ) - ‖a - 1‖) / 2)
    dsimp [r]
    linarith
  have hra : 2 * r ≤ (1 / 2 : ℝ) - ‖a - 1‖ := by
    have := min_le_right (s.re / 4) (((1 / 2 : ℝ) - ‖a - 1‖) / 2)
    dsimp [r]
    linarith
  have hKδ : ∀ z ∈ closedBall s (s.re / 2), s.re / 2 ≤ z.re := by
    intro z hz
    have hz' : ‖z - s‖ ≤ s.re / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have h := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz')).1
    simp only [Complex.sub_re] at h
    linarith
  have hball : ∀ p ∈ ball (s, a) (2 * r),
      p.1 ∈ closedBall s (s.re / 2) ∧ ‖p.2 - 1‖ ≤ (1 / 2 : ℝ) := by
    intro p hp
    have hp' := max_lt_iff.mp (show max (dist p.1 s) (dist p.2 a) < 2 * r by
      simpa only [mem_ball, Prod.dist_eq] using hp)
    constructor
    · exact (hp'.1.le.trans hrs)
    · have hn := norm_add_le (p.2 - a) (a - 1)
      have hdist : ‖p.2 - a‖ < 2 * r := by simpa only [dist_eq_norm] using hp'.2
      rw [sub_add_sub_cancel] at hn
      linarith
  obtain ⟨C, _, hC⟩ := exists_remainder_zero_bound_on_compact
    (isCompact_closedBall s (s.re / 2)) hKδ
  have hu : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(s.re / 2 + 1))) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(s.re / 2 + 1))) 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  apply GaloisForLFunctions.HTGeometry.contDiffAt_one_tsum_of_ball_bound hr
    (u := fun n => C * ((n + 1 : ℕ) : ℝ) ^ (-(s.re / 2 + 1)))
  · intro n p hp
    apply analyticAt_remainder_zero_joint
    have hb := (hball p hp).2
    have hre := (abs_le.mp ((Complex.abs_re_le_norm (p.2 - 1)).trans hb)).1
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  · exact hu.mul_left C
  · intro n p hp
    exact hC n p.1 (hball p hp).1 p.2 (hball p hp).2

/-- Joint complex `C¹` regularity of canonical continued Hurwitz zeta near its anchor. -/
theorem contDiffAt_one_continuedHzeta_joint {s a : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (ha : ‖a - 1‖ < (1 / 2 : ℝ)) :
    ContDiffAt ℂ 1 (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, a) := by
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hc := (contDiffAt_one_tsum_remainder_zero hs ha).add
    (hz.comp analyticAt_fst).contDiffAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [((isOpen_lt continuous_const
    (Complex.continuous_re.comp continuous_fst)).mem_nhds hs)] with p hp
  simp only [continuedHzeta, regularizationOrder_eq_zero hp, continuedAt, restoration_zero,
    Function.comp_def]

end HurwitzZetaContinuation
