import GaloisForLFunctions.RHTower.EvenIndexHermitianDyadicOrbit
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.HTGeometry.BoundedCoefficientLaplaceMellin

/-!
# The Liouville dyadic Gram law

Complete multiplicativity gives the Liouville coefficients the dyadic recursion
`λ (2 n) = - λ n`, so the general dyadic channel decomposition specialises to the pair of adjacent
real squares

`∑_q (∑_{a+b=2q} λ a λ b) r^{2q} = (F r + F (r ^ (2 : ℕ))) ^ (2 : ℕ) + F (r ^ (2 : ℕ)) ^ (2 : ℕ)`

(`tsum_evenIndex_binary_liouville_eq_dyadicGram`), and the orbit classification exhibits the whole
Liouville Abel series as the alternating geometric orbit of its odd seed
(`hasSum_dyadicOrbit_liouville`).
-/

open Complex Filter
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The Liouville dyadic recursion. -/
theorem liouvilleC_two_mul (n : ℕ) : liouvilleC (2 * n) = -liouvilleC n := by
  rw [liouvilleC_mul, liouvilleC_two, neg_one_mul]

theorem liouvilleC_apply_zero : (fun n : ℕ => liouvilleC n) 0 = 0 := by simp

theorem summable_norm_liouvilleC_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => ‖liouvilleC n * (r : ℂ) ^ n‖ :=
  GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow norm_liouvilleC_le_one hr0 hr1

/-- **The Liouville dyadic Gram law.**  The even additive channel of the Liouville function is the
sum of two adjacent real dyadic squares. -/
theorem tsum_evenIndex_binary_liouville_eq_dyadicGram {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' q : ℕ,
        mixedAdditiveConvolutionPower (fun n : ℕ => liouvilleC n) 1 (2 * q) * (r : ℂ) ^ (2 * q))
      = (abelSeries (fun n : ℕ => liouvilleC n) (r : ℂ)
            + abelSeries (fun n : ℕ => liouvilleC n) ((r : ℂ) ^ (2 : ℕ))) ^ (2 : ℕ)
        + abelSeries (fun n : ℕ => liouvilleC n) ((r : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) :=
  tsum_evenIndex_binary_eq_dyadicGram_neg_one conj_liouvilleC liouvilleC_two_mul r
    (summable_norm_liouvilleC_mul_pow hr0 hr1)

/-- **The Liouville dyadic orbit.**  For `0 < r < 1` the Liouville Abel series is the alternating
geometric orbit sum of its odd seed along the dyadic dilates. -/
theorem hasSum_dyadicOrbit_liouville {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasSum (fun j : ℕ =>
        (-1 : ℂ) ^ j * oddSeed (fun n : ℕ => liouvilleC n) ((r : ℂ) ^ (2 ^ j)))
      (abelSeries (fun n : ℕ => liouvilleC n) (r : ℂ)) := by
  refine hasSum_dyadicOrbit liouvilleC_apply_zero (fun n => ?_)
    (fun y hy0 hy1 => summable_norm_liouvilleC_mul_pow hy0 hy1) hr0 hr1
  rw [liouvilleC_two_mul n]
  ring

end

end RHTower
