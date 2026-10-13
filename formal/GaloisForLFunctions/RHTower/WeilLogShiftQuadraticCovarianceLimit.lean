import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticObservableMoments
import GaloisForLFunctions.RHTower.WeilLogShiftTiltVarianceKernel
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltEntropyLimit

/-! Quadratic covariance has a rank-one limit, with an exact diagonal-sum kernel. -/

open MeasureTheory ProbabilityTheory Filter Topology
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_covariance
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (h j l H J L : ℝ) :
    Tendsto (fun r => covariance (finiteWeilJointQuadratic h j l) (finiteWeilJointQuadratic H J L)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (2 * (h + 2 * j + l) * (H + 2 * J + L) *
        (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2)) := by
  have hlim := (tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_product_moment
    t a b d h j l H J L).sub
      ((tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_moment t a b d h j l).mul
        (tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_moment t a b d H J L))
  have htarget : 3 * (h + 2 * j + l) * (H + 2 * J + L) *
      (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 -
        ((h + 2 * j + l) / (4 - 2 * (a + 2 * b + d.val))) *
        ((H + 2 * J + L) / (4 - 2 * (a + 2 * b + d.val))) =
      2 * (h + 2 * j + l) * (H + 2 * J + L) *
        (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 := by ring
  rw [htarget] at hlim
  exact hlim.congr fun r => (covariance_eq_sub
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val (finiteWeilJointQuadratic h j l))
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val (finiteWeilJointQuadratic H J L))).symm

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_variance
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (h j l : ℝ) :
    Tendsto (fun r => variance (finiteWeilJointQuadratic h j l)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (2 * (h + 2 * j + l) ^ 2 * (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2)) := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_covariance t a b d h j l h j l
  have htarget : 2 * (h + 2 * j + l) * (h + 2 * j + l) *
      (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 =
        2 * (h + 2 * j + l) ^ 2 * (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 := by ring
  rw [htarget] at hlim
  exact hlim.congr fun r => covariance_self
    (finiteWeilCanonicalJointQuadraticTilt_memLp_two r _ a b d.val
      (finiteWeilJointQuadratic h j l)).aemeasurable

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_variance_zero_iff
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (h j l : ℝ) :
    Tendsto (fun r => variance (finiteWeilJointQuadratic h j l)
      (finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 0) ↔ h + 2 * j + l = 0 := by
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_variance t a b d h j l
  constructor
  · intro hzero
    have heq := tendsto_nhds_unique hlim hzero
    have hden : 0 < 4 - 2 * (a + 2 * b + d.val) := by linarith only [d.property]
    have hv : 0 < 1 / (4 - 2 * (a + 2 * b + d.val)) := one_div_pos.mpr hden
    by_contra hne
    have hpos : 0 < 2 * (h + 2 * j + l) ^ 2 *
        (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 :=
      mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hne)) (sq_pos_of_pos hv)
    exact (ne_of_gt hpos) heq
  · intro hzero
    simpa only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using hlim

end RHTower
