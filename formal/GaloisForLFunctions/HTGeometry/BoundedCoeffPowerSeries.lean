/-
# Power series with bounded coefficients

A complex power series whose coefficients are bounded has radius of convergence at least one, so its
sum is holomorphic on the open unit disc.  Only the bound on the coefficients is used; no decay is
needed.
-/
import Mathlib

noncomputable section

open Filter Metric Topology

namespace GaloisForLFunctions.HTGeometry

/-- The sum of a power series on the open unit disc. -/
def boundedFun (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, a n * z ^ n

/-- The associated formal power series. -/
def boundedSeries (a : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ a

variable {a : ℕ → ℂ} {M : ℝ}

theorem summable_boundedTerms (ha : ∀ n, ‖a n‖ ≤ M) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => a n * z ^ n) := by
  refine Summable.of_norm_bounded (g := fun n => M * ‖z‖ ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left M
  · intro n
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (ha n) (by positivity)

theorem boundedSeries_coeff (a : ℕ → ℂ) (n : ℕ) : (boundedSeries a).coeff n = a n := by
  have h := FormalMultilinearSeries.ofScalars_apply_eq (E := ℂ) (fun m => (a m : ℂ)) (1 : ℂ) n
  rw [FormalMultilinearSeries.coeff, boundedSeries,
    show ((1 : Fin n → ℂ)) = (fun _ : Fin n => (1:ℂ)) from rfl, h]
  simp

theorem one_le_boundedSeries_radius (ha : ∀ n, ‖a n‖ ≤ M) : 1 ≤ (boundedSeries a).radius := by
  have h := (boundedSeries a).le_radius_of_bound M (r := 1) (fun n => ?_)
  · simpa using h
  · rw [boundedSeries, FormalMultilinearSeries.ofScalars_norm]
    simpa using ha n

theorem eball_one_eq' (x : ℂ) : Metric.eball x (1 : ENNReal) = Metric.ball x 1 := by
  rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp, Metric.eball_ofReal]

theorem hasFPowerSeriesOnBall_boundedFun (ha : ∀ n, ‖a n‖ ≤ M) :
    HasFPowerSeriesOnBall (boundedFun a) (boundedSeries a) 0 1 where
  r_le := one_le_boundedSeries_radius ha
  r_pos := by norm_num
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < 1 := by
      have hb : y ∈ Metric.ball (0 : ℂ) 1 := by rwa [eball_one_eq'] at hy
      simpa [Metric.mem_ball, dist_zero_right] using hb
    have hs := (summable_boundedTerms ha hy').hasSum
    rw [zero_add]
    refine hs.congr_fun fun n => ?_
    rw [boundedSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **A power series with bounded coefficients is holomorphic on the open unit disc.** -/
theorem differentiableOn_boundedFun (ha : ∀ n, ‖a n‖ ≤ M) :
    DifferentiableOn ℂ (boundedFun a) (Metric.ball 0 1) := by
  intro z hz
  have hball : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by rwa [eball_one_eq']
  exact (((hasFPowerSeriesOnBall_boundedFun ha).analyticAt_of_mem
    hball).differentiableAt).differentiableWithinAt

end GaloisForLFunctions.HTGeometry
