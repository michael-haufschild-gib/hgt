import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference
import GaloisForLFunctions.HTGeometry.FiniteModalHankelRank

/-!
# Coalescing exponential poles

Exponential divided differences remove the pole in a normalized pair of nearby modes.
The second divided difference gives an explicit confluence error bound. Sampling the limit
produces a polynomial times a geometric sequence, with a nonsingular Hankel block of size two.
-/

open scoped BigOperators Matrix Topology
open GaloisForLFunctions.HTGeometry HTGeometry Filter
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

/-- A pair of exponential poles, normalized before the poles coalesce. -/
def confluentPolePair (a h u : ℝ) : ℝ :=
  u * Real.exp (-a * u) * expDivOne (-h * u)

private theorem first_second_divdiff (x : ℝ) :
    expDivOne x = 1 + x * expDivTwo x := by
  by_cases hx : x = 0
  · subst x; rw [expDivOne_zero]; ring
  · rw [expDivOne_eq_of_ne hx, expDivTwo_eq_of_ne hx]
    field_simp
    ring

/-- The apparent pole is removable, including at zero observation time. -/
theorem confluentPolePair_identity (a h u : ℝ) :
    h * confluentPolePair a h u = Real.exp (-a * u) - Real.exp (-(a + h) * u) := by
  by_cases hx : -h * u = 0
  · rcases mul_eq_zero.mp hx with hh | hu
    · have : h = 0 := neg_eq_zero.mp hh
      subst h; simp
    · subst u; simp [confluentPolePair]
  · have hh : h ≠ 0 := by intro hh; apply hx; simp [hh]
    have hu : u ≠ 0 := by intro hu; apply hx; simp [hu]
    rw [confluentPolePair, expDivOne_eq_of_ne hx,
      show -(a + h) * u = -a * u + -h * u by ring, Real.exp_add]
    field_simp [hh, hu]
    ring

/-- Coalescing simple poles create a polynomial times an exponential. -/
theorem confluentPolePair_zero (a u : ℝ) :
    confluentPolePair a 0 u = u * Real.exp (-a * u) := by
  simp only [confluentPolePair, neg_zero, zero_mul, expDivOne_zero, mul_one]

/-- Exact second divided difference controls the confluence error. -/
theorem confluentPolePair_error (a h u : ℝ) :
    confluentPolePair a h u - u * Real.exp (-a * u) =
      -h * u ^ 2 * Real.exp (-a * u) * expDivTwo (-h * u) := by
  rw [confluentPolePair, first_second_divdiff]
  ring

/-- Nonnegative pole separation has a quadratic observation-time error with constant `1/2`. -/
theorem confluentPolePair_error_bound (a delta x : ℝ) :
    |confluentPolePair a (delta ^ 2) (x ^ 2) - x ^ 2 * Real.exp (-a * x ^ 2)| ≤
      delta ^ 2 * x ^ 4 * Real.exp (-a * x ^ 2) / 2 := by
  rw [confluentPolePair_error]
  have hn : -(delta ^ 2) * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _)
  rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg delta),
    abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _),
    abs_of_pos (expDivTwo_pos hn)]
  calc
    _ ≤ delta ^ 2 * (x ^ 2) ^ 2 * Real.exp (-a * x ^ 2) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (expDivTwo_le_half hn) (by positivity)
    _ = _ := by ring


/-- The normalized pole pair converges to its confluent mode, with the displayed error bound. -/
theorem confluentPolePair_tendsto (a x : ℝ) :
    Tendsto (fun delta : ℝ => confluentPolePair a (delta ^ 2) (x ^ 2)) (𝓝 0)
      (𝓝 (x ^ 2 * Real.exp (-a * x ^ 2))) := by
  have hc : Continuous (fun delta : ℝ => delta ^ 2 * x ^ 4 * Real.exp (-a * x ^ 2) / 2) := by
    fun_prop
  have ht : Tendsto (fun delta : ℝ => delta ^ 2 * x ^ 4 * Real.exp (-a * x ^ 2) / 2)
      (𝓝 0) (𝓝 0) := by simpa using hc.continuousAt.tendsto (x := 0)
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [Metric.tendsto_nhds.mp ht eps heps] with delta hd
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (confluentPolePair_error_bound a delta x)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
    0 ≤ delta ^ 2 * x ^ 4 * Real.exp (-a * x ^ 2) / 2)] using hd

/-- The confluent sampled mode is still of order two, despite its single distinct pole. -/
def confluentModalSequence (a : ℝ) (n : ℕ) : ℝ := (n : ℝ) * Real.exp (-a) ^ n


theorem confluentModalSequence_sample (a : ℝ) (n : ℕ) :
    confluentPolePair a 0 n = confluentModalSequence a n := by
  rw [confluentPolePair_zero, confluentModalSequence]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_succ, mul_add, mul_one, Real.exp_add, ih, pow_succ]

theorem confluentModalSequence_recurrence (a : ℝ) (n : ℕ) :
    confluentModalSequence a (n + 2) - 2 * Real.exp (-a) * confluentModalSequence a (n + 1) +
      Real.exp (-a) ^ 2 * confluentModalSequence a n = 0 := by
  simp only [confluentModalSequence, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_add]
  ring

theorem confluentModalSequence_det_two (a : ℝ) :
    (algebraicHankelMatrix (confluentModalSequence a) 2).det = -(Real.exp (-a)) ^ 2 := by
  rw [Matrix.det_fin_two]
  norm_num [algebraicHankelMatrix, confluentModalSequence]
  ring

theorem confluentModalSequence_det_two_ne_zero (a : ℝ) :
    (algebraicHankelMatrix (confluentModalSequence a) 2).det ≠ 0 := by
  rw [confluentModalSequence_det_two]
  exact neg_ne_zero.mpr (pow_ne_zero _ (Real.exp_ne_zero _))

#print axioms confluentPolePair_identity
#print axioms confluentPolePair_error_bound
#print axioms confluentPolePair_tendsto
#print axioms confluentModalSequence_sample
#print axioms confluentModalSequence_recurrence
#print axioms confluentModalSequence_det_two_ne_zero

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
