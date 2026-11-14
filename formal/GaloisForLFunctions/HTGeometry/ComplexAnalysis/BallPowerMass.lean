import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq

/-!
# Exact power mass on a complex disk

The polar formula evaluates every nonnegative integral power of the radius. In particular,
`∫_{|z|<R} |z|^(2m) = π R^(2m+2)/(m+1)`. This gives an exact test for finite vanishing
order and supplies the planar radial factor in compensated-slice identities.
-/

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

/-- The even power of the radius has an exact disk integral. -/
theorem integral_ball_norm_even_pow (m : ℕ) (R : NNReal) :
    (∫ z in Metric.ball (0 : ℂ) R, ‖z‖ ^ (2 * m)) =
      Real.pi * (R : ℝ) ^ (2 * m + 2) / (m + 1) := by
  rw [integral_ball_continuous_eq_shell (fun z => ‖z‖ ^ (2 * m))
    (continuous_norm.pow _) R]
  have hinner (r : ℝ) (hr : 0 ≤ r) :
      (∫ θ in Ioo (-Real.pi) Real.pi, ‖circleMap 0 r θ‖ ^ (2 * m)) =
        (2 * Real.pi) * r ^ (2 * m) := by
    simp only [norm_circleMap_zero, abs_of_nonneg hr, integral_const, smul_eq_mul]
    have hvol : (volume.restrict (Ioo (-Real.pi) Real.pi)).real univ = 2 * Real.pi := by
      calc
        _ = volume.real (Ioo (-Real.pi) Real.pi) := by simp [Measure.real]
        _ = _ := by
          rw [Real.volume_real_Ioo, max_eq_left (by linarith [Real.pi_pos])]
          ring
    rw [hvol]
  have hradial :
      (∫ r in Ioo (0 : ℝ) R, r • ∫ θ in Ioo (-Real.pi) Real.pi,
        ‖circleMap 0 r θ‖ ^ (2 * m)) =
      ∫ r in Ioo (0 : ℝ) R, (2 * Real.pi) * r ^ (2 * m + 1) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [hinner r hr.1.le, smul_eq_mul, pow_succ]
    ring
  rw [hradial, show (∫ r in Ioo (0 : ℝ) R, (2 * Real.pi) * r ^ (2 * m + 1)) =
      ∫ r in (0 : ℝ)..R, (2 * Real.pi) * r ^ (2 * m + 1) by
    rw [intervalIntegral.integral_of_le R.coe_nonneg]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp only [zero_pow (by omega : 2 * m + 1 + 1 ≠ 0), sub_zero]
  push_cast
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (2 * m + 1 + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
