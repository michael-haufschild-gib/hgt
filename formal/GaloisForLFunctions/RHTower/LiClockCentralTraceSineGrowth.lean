import GaloisForLFunctions.RHTower.LiClockCentralTraceSineReflection
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Growth and normalized decay of the central trace sine contour

A trace holomorphic on a larger disk and continuous on its closure has the same literal
negative sine contour on every positive smaller radius. The installed odd-derivative series
identifies the radii, while a compact bound on the larger source circle gives the sharp
`sinh` envelope. Every strictly larger exponential rate makes the real-clock complex response
converge to zero. No source parity or logarithm branch is assumed.
-/

open Complex Set Metric Filter Topology

namespace RHTower

/-- The same trace germ gives exactly the same sine contour on every smaller positive radius. -/
theorem liClockCentralTraceSineContour_radius_eq {r ρ : ℝ} (hr : 0 < r)
    (hrρ : r ≤ ρ) {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 ρ)) (t : ℂ) :
    liClockCentralTraceSineContour T r t = liClockCentralTraceSineContour T ρ t := by
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr (hT.mono (ball_subset_ball hrρ)),
    liClockCentralTraceSineContour_eq_neg_tsum (hr.trans_le hrρ) hT]

/-- A bound on the larger source circle controls every complex clock with its exact `sinh` rate. -/
theorem exists_liClockCentralTraceSineContour_growth_bound {r ρ : ℝ} (hr : 0 < r)
    (hrρ : r ≤ ρ) {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 ρ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℂ,
      ‖liClockCentralTraceSineContour T r t‖ ≤ M * Real.sinh (‖t‖ / ρ) := by
  have hTc : ContinuousOn T (sphere 0 ρ) :=
    hT.continuousOn_ball.mono sphere_subset_closedBall
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) ρ).bddAbove_image hTc.norm
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, fun t => ?_⟩
  have hbound (z : ℂ) (hz : z ∈ sphere (0 : ℂ) ρ) : ‖T z - 0‖ ≤ M := by
    simpa only [sub_zero] using (hC ⟨z, hz, rfl⟩).trans (le_max_left C 0)
  have hzero : liClockCentralTraceSineContour (fun _ : ℂ => 0) ρ t = 0 := by
    simp [liClockCentralTraceSineContour, circleIntegral]
  rw [liClockCentralTraceSineContour_radius_eq hr hrρ hT]
  simpa only [hzero, sub_zero] using
    norm_liClockCentralTraceSineContour_sub_le (hr.trans_le hrρ) hM hTc
      (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℂ)) (sphere 0 ρ)) hbound t

/-- A larger analytic disk makes every strictly faster exponential-normalized contour decay. -/
theorem liClockCentralTraceSineContour_exp_neg_mul_tendsto_zero {r ρ k : ℝ}
    (hr : 0 < r) (hrρ : r ≤ ρ) {T : ℂ → ℂ}
    (hT : DiffContOnCl ℂ T (ball 0 ρ)) (hk : 1 / ρ < k) :
    Tendsto (fun t : ℝ => (Real.exp (-k * t) : ℂ) *
      liClockCentralTraceSineContour T r (t : ℂ)) atTop (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ := exists_liClockCentralTraceSineContour_growth_bound hr hrρ hT
  have hrate : 0 < k - 1 / ρ := sub_pos.mpr hk
  have hdecay : Tendsto (fun t : ℝ => M * Real.exp (-(k - 1 / ρ) * t))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hrate)).const_mul M
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdecay
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hb : ‖liClockCentralTraceSineContour T r (t : ℂ)‖ ≤ M * Real.sinh (t / ρ) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht] using hbound (t : ℂ)
  have hsinh : Real.sinh (t / ρ) ≤ Real.exp (t / ρ) := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (t / ρ), Real.exp_pos (-(t / ρ))]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    Real.exp (-k * t) * ‖liClockCentralTraceSineContour T r (t : ℂ)‖ ≤
        Real.exp (-k * t) * (M * Real.sinh (t / ρ)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ ≤ Real.exp (-k * t) * (M * Real.exp (t / ρ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsinh hM) (Real.exp_pos _).le
    _ = M * Real.exp (-(k - 1 / ρ) * t) := by
      rw [show Real.exp (-k * t) * (M * Real.exp (t / ρ)) =
        M * (Real.exp (-k * t) * Real.exp (t / ρ)) by ring, ← Real.exp_add]
      congr 2
      ring

/-- Every positive-rate real hyperbolic sine has normalized leading coefficient one half. -/
theorem liClock_exp_neg_mul_sinh_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.exp (-a * t) * Real.sinh (a * t))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hid (t : ℝ) : Real.exp (-a * t) * Real.sinh (a * t) =
      (1 - Real.exp (-(2 * a) * t)) / 2 := by
    rw [Real.sinh_eq]
    calc
      Real.exp (-a * t) * ((Real.exp (a * t) - Real.exp (-(a * t))) / 2) =
          (Real.exp (-a * t) * Real.exp (a * t) -
            Real.exp (-a * t) * Real.exp (-(a * t))) / 2 := by ring
      _ = (1 - Real.exp (-(2 * a) * t)) / 2 := by
        rw [← Real.exp_add, ← Real.exp_add]
        rw [show -a * t + a * t = 0 by ring,
          show -a * t + -(a * t) = -(2 * a) * t by ring, Real.exp_zero]
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-(2 * a) * t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (mul_pos (by norm_num : (0 : ℝ) < 2) ha))
  simpa only [hid, sub_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hdecay).div_const 2

/-- The same exact leading coefficient holds in the complex codomain along real clocks. -/
theorem liClock_exp_neg_mul_complex_sinh_ofReal_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => (Real.exp (-a * t) : ℂ) * Complex.sinh ((a : ℂ) * (t : ℂ)))
      atTop (𝓝 (1 / 2 : ℂ)) := by
  simpa only [Function.comp_def, Complex.ofReal_mul, Complex.ofReal_sinh,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    (Complex.continuous_ofReal.tendsto (1 / 2 : ℝ)).comp (liClock_exp_neg_mul_sinh_tendsto ha)

end RHTower

