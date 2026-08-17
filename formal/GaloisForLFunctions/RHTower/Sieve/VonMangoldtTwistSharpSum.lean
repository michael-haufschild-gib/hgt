import GaloisForLFunctions.RHTower.Sieve.SmoothedPartialSumConnector
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPerron

/-!
# The sharp twisted Chebyshev sum

A contour argument bounds the *smoothly* cut series; a mean value theorem is a statement about the
sharp partial sum.  The two differ only on the transition window `(K, ⌊K+H⌋]`, so the transport
costs the window width times the size of the coefficients there.

The corpus's connector assumes `‖f‖ ≤ 1`, which the von Mangoldt function does not satisfy.  The
transport never needs more than a bound on the window, so it is restated with a general constant;
for `Λ(n)n^{-iτ}` that constant is `log(K+H)`, and removing the smoothing costs `H·log(K+H)`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction GaloisForLFunctions

/-- **From a smoothed bound to a sharp one, with a general coefficient bound.**  The unit bound on
the coefficients is stronger than the transport needs: only their size on the transition window
matters, and the cost is that size times the window width. -/
theorem norm_partialSum_le_of_smoothed_bound_of_le {f : ℕ → ℂ} {K : ℕ} {H C : ℝ}
    (hH : 0 < H) (hC : 0 ≤ C)
    (hbdd : ∀ n, K < n → n ≤ ⌊(K : ℝ) + H⌋₊ → ‖f n‖ ≤ C) {B : ℝ}
    (hB : (2 * Real.pi) *
        ‖∑' n : ℕ, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ ≤ B) :
    ‖∑ n ∈ Finset.range (K + 1), f n‖ ≤ B / (2 * Real.pi) + C * H := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set m : ℕ := ⌊(K : ℝ) + H⌋₊ + 1 with hmdef
  have hm : (K : ℝ) + H ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one ((K : ℝ) + H)
    rw [hmdef]
    push_cast
    linarith
  have hsum := tsum_mul_smoothWeight_eq_sum_range (a := f) hH K m hm
  have hwin : ‖(∑ n ∈ Finset.range m,
        f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      - ∑ n ∈ Finset.range (K + 1), f n‖ ≤ ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * C :=
    norm_weighted_sub_partialSum_le_uniform hH K m hm hbdd
  have hsmooth : ‖∑' n : ℕ, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
      ≤ B / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm]
    exact hB
  have hsplit : ‖∑ n ∈ Finset.range (K + 1), f n‖
      ≤ ‖∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        + ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * C := by
    have h := norm_sub_norm_le (∑ n ∈ Finset.range (K + 1), f n)
      (∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
    have hrev : ‖(∑ n ∈ Finset.range (K + 1), f n)
        - ∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        = ‖(∑ n ∈ Finset.range m,
              f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
            - ∑ n ∈ Finset.range (K + 1), f n‖ := norm_sub_rev _ _
    rw [hrev] at h
    linarith [h, hwin]
  rw [← hsum] at hsplit
  have hwidth : ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * C ≤ C * H := by
    have := card_smoothing_window_le (K := K) hH
    nlinarith [Nat.cast_nonneg (α := ℝ) (⌊(K : ℝ) + H⌋₊ - K)]
  linarith [hsplit, hsmooth, hwidth]

/-- The twisted von Mangoldt coefficients on the transition window are at most `log(K+H)`. -/
theorem norm_vonMangoldtTwist_le_log (τ : ℝ) {K : ℕ} {H : ℝ} (hKH : 1 ≤ (K : ℝ) + H)
    {n : ℕ} (hn : K < n) (hnm : n ≤ ⌊(K : ℝ) + H⌋₊) :
    ‖vonMangoldtTwist τ n‖ ≤ Real.log ((K : ℝ) + H) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hle : (n : ℝ) ≤ (K : ℝ) + H := by
    have h1 : ((n : ℕ) : ℝ) ≤ ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnm
    exact h1.trans (Nat.floor_le (by linarith))
  rw [norm_vonMangoldtTwist]
  exact vonMangoldt_le_log.trans (Real.log_le_log hnR hle)

/-- **The sharp twisted Chebyshev sum from a smoothed bound.**  Removing the smoothing costs the
window width times the largest von Mangoldt value it can meet. -/
theorem norm_partialSum_vonMangoldtTwist_le_of_smoothed_bound (τ : ℝ) {K : ℕ} {H : ℝ}
    (hH : 0 < H) (hKH : 1 ≤ (K : ℝ) + H) {B : ℝ}
    (hB : (2 * Real.pi) * ‖∑' n : ℕ,
        vonMangoldtTwist τ n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ ≤ B) :
    ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖
      ≤ B / (2 * Real.pi) + Real.log ((K : ℝ) + H) * H :=
  norm_partialSum_le_of_smoothed_bound_of_le hH (Real.log_nonneg hKH)
    (fun _ hn hnm => norm_vonMangoldtTwist_le_log τ hKH hn hnm) hB

end RHTower.Sieve
