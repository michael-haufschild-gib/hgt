import GaloisForLFunctions.RHTower.Sieve.MoebiusSmoothLittleO
import GaloisForLFunctions.HTGeometry.SmoothWeightWindow

/-!
# The smoothed sum against the sharp sum

The cutoff is `1` below `N` and `0` above `N + H`, so the smoothed Möbius sum and the sharp sum
`∑_{n ≤ N} μ(n)` differ only over the transition window, where the summand is at most `1` in modulus.
The window contains at most `H + 1` integers, so

    ‖ ∑ₙ μ(n)·w(n) - ∑_{n ≤ N} μ(n) ‖ ≤ H + 1.

This is the only step that compares the two sums, and it is entirely elementary — no analysis enters.
It is the unimodular case of the real-cutoff window law
`GaloisForLFunctions.HTGeometry.norm_tsum_mul_smoothWeight_sub_partialSum_le_width`, which allows an
arbitrary uniform bound on the coefficients of the window.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The smoothed and sharp sums of a unimodular sequence differ by at most the window length.** -/
theorem norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one {a : ℕ → ℂ} (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    ‖(∑' n : ℕ, a n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), a n‖
      ≤ H + 1 := by
  simpa using norm_tsum_mul_smoothWeight_sub_partialSum_le_width hN.le hH zero_le_one
    (fun n _ _ => ha n)

/-- **The smoothed and sharp Möbius sums differ by at most the window length.** -/
theorem norm_tsum_smoothWeight_sub_sum_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) :
    ‖(∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (⌊N⌋₊ + 1), (ArithmeticFunction.moebius n : ℂ)‖
      ≤ H + 1 := by
  refine norm_tsum_smoothWeight_sub_sum_le_of_norm_le_one ?_ hN hH
  intro n
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end RHTower.Sieve
