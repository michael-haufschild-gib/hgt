import GaloisForLFunctions.HTGeometry.RealPowerSumRigidity
import GaloisForLFunctions.HTGeometry.GaussianContinuousVarianceRigidity
import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments

/-! Nonzero combinations of positive powers have strictly nonzero Gaussian variance. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem gaussianZero_memLp_two_nat_pow (v : NNReal) (k : ℕ) :
    MemLp (fun x : ℝ => x ^ k) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simp only [← pow_mul]
  exact gaussianZero_integrable_nat_pow v (k * 2)

theorem gaussianZero_variance_power_sum_zero_iff
    (v : NNReal) (hv : v ≠ 0) (n : ℕ) (c : Fin n → ℝ) :
    variance (fun x : ℝ => ∑ i : Fin n, c i * x ^ ((i : ℕ) + 1))
      (gaussianReal 0 v) = 0 ↔ c = 0 := by
  have hmem : MemLp (fun x : ℝ => ∑ i : Fin n, c i * x ^ ((i : ℕ) + 1))
      2 (gaussianReal 0 v) :=
    memLp_finsetSum Finset.univ fun i _ =>
      (gaussianZero_memLp_two_nat_pow v ((i : ℕ) + 1)).const_mul (c i)
  rw [gaussianReal_variance_eq_zero_iff_constant 0 v hv (by fun_prop) hmem]
  have hzero : (∑ i : Fin n, c i * (0 : ℝ) ^ ((i : ℕ) + 1)) = 0 := by simp
  simpa only [hzero] using real_power_sum_succ_eq_zero_iff n c

end GaloisForLFunctions.HTGeometry
