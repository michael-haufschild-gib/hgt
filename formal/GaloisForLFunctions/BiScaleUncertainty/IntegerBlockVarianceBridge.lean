import GaloisForLFunctions.BiScaleUncertainty.DyadicBlockEnergyDiscreteDeviation
import GaloisForLFunctions.BiScaleUncertainty.IntegerBlockVariance

/-!
# The fine block energy as the in-block variance of the integer Chebyshev error

With `u_j = E(X + j)` (`E(n) = ψ(n) − n`) on the dyadic block `[X, 2X)`, the deviation sum of the
field and the finite block variance `Σ_{r<s<X} (u_r − u_s)² = X Σ u_r² − (Σ u_r)²` of the parallel
integer-block programme are related exactly:

`X · Σ_{j<X} (u_j − u_0)² = finiteBlockVariance X u + (Σ_{j<X} u_j − X u_0)²`.

Hence the fine block energy `c_k` of the renewal chain (`X = 2^k`) is, up to constants and `O(1)`,

`Var_X(E) / X³ + (Ē_X − E(X))² / X`,

the in-block variance of the integer Chebyshev error normalized by `X³`, plus the squared deviation
of the block mean from the block-start value normalized by `X`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar

noncomputable section
set_option autoImplicit false

/-- The block sequence `u_j = E(X + j)`. -/
def blockErrorSeq (X : ℕ) : ℕ → ℝ := fun j => cellError (X + j)

theorem blockDeviationSum_eq_sum_range (X : ℕ) :
    blockDeviationSum X = ∑ j ∈ Finset.range X, (blockErrorSeq X j - blockErrorSeq X 0) ^ 2 := by
  unfold blockDeviationSum blockErrorSeq
  rw [Finset.sum_Ico_eq_sum_range, show 2 * X - X = X by omega]
  simp only [add_zero]

/-- **Exact variance decomposition of the deviation sum:**
`X · D_X = finiteBlockVariance X u + (Σ_{j<X} u_j − X u_0)²`. -/
theorem mul_blockDeviationSum_eq_finiteBlockVariance_add (X : ℕ) :
    (X : ℝ) * blockDeviationSum X =
      SobolevShear.finiteBlockVariance X (blockErrorSeq X) +
        ((∑ j ∈ Finset.range X, blockErrorSeq X j) - X * blockErrorSeq X 0) ^ 2 := by
  rw [blockDeviationSum_eq_sum_range, SobolevShear.finiteBlockVariance_eq]
  have hexp : (∑ j ∈ Finset.range X, (blockErrorSeq X j - blockErrorSeq X 0) ^ 2) =
      (∑ j ∈ Finset.range X, blockErrorSeq X j ^ 2) -
        2 * blockErrorSeq X 0 * (∑ j ∈ Finset.range X, blockErrorSeq X j) +
        X * blockErrorSeq X 0 ^ 2 := by
    have : ∀ j ∈ Finset.range X, (blockErrorSeq X j - blockErrorSeq X 0) ^ 2 =
        blockErrorSeq X j ^ 2 - 2 * blockErrorSeq X 0 * blockErrorSeq X j +
          blockErrorSeq X 0 ^ 2 := fun j _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hexp]
  ring

theorem finiteBlockVariance_le_mul_blockDeviationSum (X : ℕ) :
    SobolevShear.finiteBlockVariance X (blockErrorSeq X) ≤ (X : ℝ) * blockDeviationSum X := by
  rw [mul_blockDeviationSum_eq_finiteBlockVariance_add]
  nlinarith [sq_nonneg ((∑ j ∈ Finset.range X, blockErrorSeq X j) - X * blockErrorSeq X 0)]

/-- **The dyadic fine block energy is controlled below by the in-block variance:**
`Var_X(E)/(16 X³) − 2 ≤ c_k`. -/
theorem finiteBlockVariance_div_le_blockEnergy (N : ℕ) {k : ℕ}
    (hk : (k + 1) * Real.log 2 ≤ cutoff N) :
    SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) /
        (16 * (((2 ^ k : ℕ) : ℝ)) ^ 3) - 2 ≤
      blockEnergy N (Real.log 2) k := by
  have h := (blockEnergy_log_two_bounds N hk).1
  have hX0 : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hv := finiteBlockVariance_le_mul_blockDeviationSum (2 ^ k)
  have hdiv : SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) /
      (16 * (((2 ^ k : ℕ) : ℝ)) ^ 3) ≤
      blockDeviationSum (2 ^ k) / (16 * (((2 ^ k : ℕ) : ℝ)) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hv, hX0, pow_pos hX0 2, mul_le_mul_of_nonneg_right hv (le_of_lt (pow_pos hX0 2))]
  linarith

/-- **The dyadic fine block energy is controlled above by the variance and the mean deviation:**
`c_k ≤ 4 Var_X(E)/X³ + 4 (Σ u_j − X u_0)²/X³ + 10`. -/
theorem blockEnergy_le_finiteBlockVariance_add (N : ℕ) {k : ℕ}
    (hk : (k + 1) * Real.log 2 ≤ cutoff N) :
    blockEnergy N (Real.log 2) k ≤
      4 * SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) /
          (((2 ^ k : ℕ) : ℝ)) ^ 3 +
        4 * ((∑ j ∈ Finset.range (2 ^ k), blockErrorSeq (2 ^ k) j) -
          ((2 ^ k : ℕ) : ℝ) * blockErrorSeq (2 ^ k) 0) ^ 2 / (((2 ^ k : ℕ) : ℝ)) ^ 3 + 10 := by
  have h := (blockEnergy_log_two_bounds N hk).2
  have hX0 : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hid := mul_blockDeviationSum_eq_finiteBlockVariance_add (2 ^ k)
  have hD : blockDeviationSum (2 ^ k) =
      (SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) +
        ((∑ j ∈ Finset.range (2 ^ k), blockErrorSeq (2 ^ k) j) -
          ((2 ^ k : ℕ) : ℝ) * blockErrorSeq (2 ^ k) 0) ^ 2) / ((2 ^ k : ℕ) : ℝ) := by
    rw [eq_div_iff hX0.ne', mul_comm]; exact hid
  rw [hD] at h
  have e : 4 * ((SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) +
        ((∑ j ∈ Finset.range (2 ^ k), blockErrorSeq (2 ^ k) j) -
          ((2 ^ k : ℕ) : ℝ) * blockErrorSeq (2 ^ k) 0) ^ 2) / ((2 ^ k : ℕ) : ℝ)) /
        (((2 ^ k : ℕ) : ℝ)) ^ 2 =
      4 * SobolevShear.finiteBlockVariance (2 ^ k) (blockErrorSeq (2 ^ k)) /
          (((2 ^ k : ℕ) : ℝ)) ^ 3 +
        4 * ((∑ j ∈ Finset.range (2 ^ k), blockErrorSeq (2 ^ k) j) -
          ((2 ^ k : ℕ) : ℝ) * blockErrorSeq (2 ^ k) 0) ^ 2 / (((2 ^ k : ℕ) : ℝ)) ^ 3 := by
    field_simp
    ring
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
