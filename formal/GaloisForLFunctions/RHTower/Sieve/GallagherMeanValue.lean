import GaloisForLFunctions.RHTower.Sieve.GallagherSplitIntegral
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# The short-interval mean square from the mean value theorem alone

Composing the integral split of Gallagher's identity with the mean value theorem in the frequency
variable gives, with no arithmetic input whatever,

    ∫_ℝ |∑_{u < log n ≤ u+δ} a_n|² du
      ≤ 2δ²(2πW + 4N(1+log N))/π · ∑_{n ≤ N}|a_n|² + (∑_{n ≤ N}|a_n|)² · 2/(π²W)

for every frequency height `W > 0`.  Balancing the two terms in `W` beats the trivial bound
`δ·(∑|a_n|)²` by a power of `N` for the Möbius coefficients, using neither a zero-free region nor
any cancellation estimate: the whole gain comes from the diagonal of the mean value theorem.

This is the base case that every arithmetic improvement is measured against.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Finset

/-- The trivial bound on the Gallagher polynomial. -/
theorem norm_logPoly_le (a : ℕ → ℂ) (s : Finset ℕ) (w : ℝ) :
    ‖logPoly a s w‖ ≤ ∑ n ∈ s, ‖a n‖ := by
  rw [logPoly]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero, mul_one]

/-- **The short-interval mean square from the mean value theorem alone.** -/
theorem gallagher_meanValue_le (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    (∫ u : ℝ, ‖logWindowSum a (Finset.Icc 1 N) δ u‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((2 * Real.pi * W + 4 * (N : ℝ) * (1 + Real.log N)) / Real.pi
              * ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) * (2 / (Real.pi ^ (2 : ℕ) * W)) := by
  have hI := integral_Icc_normSq_logPoly_le a N (W := W) hW.le
  have hM₂ : ∀ w : ℝ, ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ)
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) := by
    intro w
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a (Finset.Icc 1 N) w) 2
  exact gallagher_split_integral a (Finset.Icc 1 N) hδ hW (by positivity) hI hM₂

/-- **The multiplicative short-interval mean square from the mean value theorem alone.** -/
theorem gallagher_meanValue_window_le (a : ℕ → ℂ) (N : ℕ) {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (A B : ℝ) :
    (∫ u in Set.Ioc (Real.log A) (Real.log B),
        ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ =>
          Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ), a n‖ ^ (2 : ℕ))
      ≤ 2 * δ ^ (2 : ℕ)
          * ((2 * Real.pi * W + 4 * (N : ℝ) * (1 + Real.log N)) / Real.pi
              * ∑ m : Fin N, ‖a ((m : ℕ) + 1)‖ ^ (2 : ℕ))
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) * (2 / (Real.pi ^ (2 : ℕ) * W)) := by
  have hI := integral_Icc_normSq_logPoly_le a N (W := W) hW.le
  have hM₂ : ∀ w : ℝ, ‖logPoly a (Finset.Icc 1 N) w‖ ^ (2 : ℕ)
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ (2 : ℕ) := by
    intro w
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a (Finset.Icc 1 N) w) 2
  have hs : ∀ n ∈ Finset.Icc 1 N, 0 < n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    omega
  exact setIntegral_normSq_multiplicative_window_le_integral a (Finset.Icc 1 N) hs hδ hW
    (by positivity) hI hM₂ A B

end RHTower.Sieve
