import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltMoments

/-! All binary homogeneous polynomial moments converge under the actual finite quadratic tilts. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators
local notation "E" => EuclideanSpace ℝ (Fin 2)

namespace RHTower

theorem tendsto_finiteWeilCanonicalJointQuadraticTilt_homogeneous_moment
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2})
    (n : ℕ) (c : Fin (n + 1) → ℝ) :
    Tendsto (fun r => ∫ z : E, ∑ i : Fin (n + 1), c i * (z 0 ^ (i : ℕ) * z 1 ^ (n - i))
      ∂(finiteWeilCanonicalJointQuadraticTilt r (2 * (r + 1) ^ 2 + t r) a b d.val : Measure E))
      atTop (𝓝 ((∑ i, c i) * (∫ x : ℝ, x ^ n ∂(gaussianReal 0
        (finiteWeilQuadraticTiltVariance ⟨a + 2 * b + d.val, d.property⟩))))) := by
  have h (i : Fin (n + 1)) :=
    (tendsto_finiteWeilCanonicalJointQuadraticTilt_mixed_moment t a b d i (n - i)).const_mul (c i)
  have hdegree (i : Fin (n + 1)) : (i : ℕ) + (n - i) = n := by omega
  simp only [hdegree] at h
  have hs := tendsto_finsetSum Finset.univ (fun i _ => h i)
  rw [← Finset.sum_mul] at hs
  refine hs.congr fun r => ?_
  rw [integral_finsetSum _ (fun i _ =>
    finiteWeilCanonicalJointQuadraticTilt_integrable r _ a b d.val _)]
  exact Finset.sum_congr rfl fun i _ => (integral_const_mul (c i) _).symm

end RHTower
