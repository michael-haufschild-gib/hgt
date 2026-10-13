import GaloisForLFunctions.RHTower.WeilLogShiftHomogeneousTiltMoments
import GaloisForLFunctions.RHTower.GaussianProbabilityFourthMoment

/-! Exact limiting product moments of arbitrary quadratic observables. -/

open MeasureTheory ProbabilityTheory Filter Topology GaloisForLFunctions.HTGeometry
open scoped BigOperators
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_quadratic_product_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) (h j l H J L : ℝ) :
    Tendsto (fun r => ∫ z : E, finiteWeilJointQuadratic h j l z * finiteWeilJointQuadratic H J L z
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 (3 * (h + 2 * j + l) * (H + 2 * J + L) *
        (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2)) := by
  let c : Fin 5 → ℝ :=
    ![l * L, 2 * (j * L + l * J), h * L + 4 * j * J + l * H, 2 * (h * J + j * H), h * H]
  have hpoly (z : E) : (∑ i : Fin 5, c i * (z 0 ^ (i : ℕ) * z 1 ^ (4 - (i : ℕ)))) =
      finiteWeilJointQuadratic h j l z * finiteWeilJointQuadratic H J L z := by
    norm_num [c, Fin.sum_univ_succ, finiteWeilJointQuadratic]
    ring
  have hsum : (∑ i, c i) = (h + 2 * j + l) * (H + 2 * J + L) := by
    norm_num [c, Fin.sum_univ_succ]
    ring
  have hvar : (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩ : ℝ) =
      1 / (4 - 2 * (a + 2 * b + d.val)) := rfl
  have htarget : ((h + 2 * j + l) * (H + 2 * J + L)) *
      (3 * (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2) =
        3 * (h + 2 * j + l) * (H + 2 * J + L) *
          (1 / (4 - 2 * (a + 2 * b + d.val))) ^ 2 := by ring
  have hlim := tendsto_finiteWeilCanonicalJointQuadraticTilt_homogeneous_moment t a b d 4 c
  simpa only [hpoly, hsum, gaussianZero_integral_fourth, hvar, htarget] using hlim

end RHTower
