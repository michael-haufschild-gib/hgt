import GaloisForLFunctions.HTGeometry.HardyDiskSpace

/-!
# The disk Bergman coefficient model

Square-summable coordinates multiply the orthonormal monomials
`sqrt (n+1) z^n` for normalized disk area. Polynomially weighted geometric
summability supplies the full unit disk of analyticity and exact Taylor
coefficient recovery. This model supports composition-operator questions
from arXiv:2610.35415 on a concrete holomorphic function space.
-/

namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry Complex Filter Metric Real Topology
noncomputable section

/-- Hilbert coordinates in the normalized Bergman monomial basis. -/
abbrev Disk := lp (fun _ : ℕ => ℂ) 2

def coefficient (a : Disk) (n : ℕ) : ℂ := (Real.sqrt (n + 1 : ℝ) : ℂ) * a n

def diskFun (a : Disk) (z : ℂ) : ℂ := ∑' n, coefficient a n * z ^ n

def diskSeries (a : Disk) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (coefficient a)

private theorem coefficient_bound (a : Disk) (n : ℕ) :
    ‖coefficient a n‖ ≤ ((n : ℝ) + 1) * ‖a‖ := by
  rw [coefficient, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sqrt_nonneg _)]
  have hs : Real.sqrt (n + 1 : ℝ) ≤ (n : ℝ) + 1 := by
    nlinarith only [sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity),
      sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  exact mul_le_mul hs (hardyDisk_norm_coord_le a n) (norm_nonneg _) (by positivity)

private theorem weighted_geometric_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).add
    (summable_geometric_of_lt_one hr0 hr1)
  simpa only [pow_one, add_mul, one_mul] using h

/-- Bergman Taylor terms converge absolutely throughout the open unit disk. -/
theorem summable_terms (a : Disk) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => coefficient a n * z ^ n) := by
  refine Summable.of_norm_bounded
    ((weighted_geometric_summable (norm_nonneg z) hz).mul_right ‖a‖) ?_
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖coefficient a n‖ * ‖z‖ ^ n ≤ (((n : ℝ) + 1) * ‖a‖) * ‖z‖ ^ n :=
      mul_le_mul_of_nonneg_right (coefficient_bound a n) (by positivity)
    _ = (((n : ℝ) + 1) * ‖z‖ ^ n) * ‖a‖ := by ring

private theorem series_norm_summable (a : Disk) {r : NNReal} (hr : r < 1) :
    Summable (fun n => ‖diskSeries a n‖ * (r : ℝ) ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) ?_
    ((weighted_geometric_summable r.coe_nonneg (by exact_mod_cast hr)).mul_right ‖a‖)
  intro n
  rw [diskSeries, FormalMultilinearSeries.ofScalars_norm]
  calc
    ‖coefficient a n‖ * (r : ℝ) ^ n ≤ (((n : ℝ) + 1) * ‖a‖) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (coefficient_bound a n) (by positivity)
    _ = (((n : ℝ) + 1) * (r : ℝ) ^ n) * ‖a‖ := by ring

/-- Polynomial coefficient growth does not shrink the convergence disk. -/
theorem one_le_radius (a : Disk) : 1 ≤ (diskSeries a).radius := by
  by_contra h
  obtain ⟨r, hr0, hr1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
  have hr : r < 1 := by exact_mod_cast hr1
  exact not_lt_of_ge ((diskSeries a).le_radius_of_summable_norm (series_norm_summable a hr)) hr0

theorem hasFPowerSeriesOnBall_diskFun (a : Disk) :
    HasFPowerSeriesOnBall (diskFun a) (diskSeries a) 0 1 where
  r_le := one_le_radius a
  r_pos := by norm_num
  hasSum := by
    intro z hz
    have hz' : ‖z‖ < 1 := by
      rw [eball_one_eq] at hz
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    rw [zero_add]
    exact (summable_terms a hz').hasSum.congr_fun fun n => by
      rw [diskSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- Every coefficient vector defines an actual holomorphic function on the disk. -/
theorem differentiableOn_diskFun (a : Disk) :
    DifferentiableOn ℂ (diskFun a) (Metric.ball 0 1) := by
  intro z hz
  have hb : z ∈ Metric.eball (0 : ℂ) (1 : ENNReal) := by rwa [eball_one_eq]
  exact ((hasFPowerSeriesOnBall_diskFun a).analyticAt_of_mem hb).differentiableAt.differentiableWithinAt

/-- The Hilbert coordinates are recovered by the actual derivatives at the origin. -/
theorem diskCoeff_diskFun (a : Disk) (n : ℕ) :
    diskCoeff (diskFun a) n = coefficient a n := by
  rw [← coeff_eq_diskCoeff (hasFPowerSeriesOnBall_diskFun a) n]
  change ((diskSeries a n) fun _ => (1 : ℂ)) = _
  rw [diskSeries, FormalMultilinearSeries.ofScalars_apply_eq]
  simp

#print axioms summable_terms
#print axioms hasFPowerSeriesOnBall_diskFun
#print axioms differentiableOn_diskFun
#print axioms diskCoeff_diskFun
end
end GaloisForLFunctions.HilbertMetric.Bergman
