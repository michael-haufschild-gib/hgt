import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients
import GaloisForLFunctions.HTGeometry.SmoothWeightWindow

/-!
# The smoothing error against a uniform coefficient bound

Replacing a sharp cutoff at `K` by the smooth weight of transition width `H` disturbs only the indices of
the window `(K, ⌊K+H⌋]`, so a uniform bound `C` on the coefficients there bounds the whole disturbance by

`‖∑_{n<m} d(n)·w(n) − ∑_{n≤K} d(n)‖ ≤ (⌊K+H⌋ − K)·C`,   `K + H ≤ m`.

For a threefold convolution two of whose factors are supported on primes the coefficients are
polylogarithmic, so `C = (log⌊K+H⌋)⁴/(log 2)²` is admissible, and for the coefficient sequences of the
Granville–Harper–Soundararajan convolution `C = (log⌊K+H⌋)⁴/(log 2)³`.  At `H = K/(log K)⁶` both bounds
read `O(K/(log K)²)`: nothing arithmetic enters, in particular no divisor estimate and no short-interval
mean value theorem.
-/

noncomputable section
namespace RHTower.Sieve
open Finset GaloisForLFunctions.HTGeometry

/-- **The smoothing error against a uniform window bound.**  Window length times coefficient size. -/
theorem norm_weighted_sub_partialSum_le_uniform {d : ℕ → ℂ} {C : ℝ} {H : ℝ} (hH : 0 < H)
    (K m : ℕ) (hm : (K : ℝ) + H ≤ (m : ℝ))
    (hd : ∀ n, K < n → n ≤ ⌊(K : ℝ) + H⌋₊ → ‖d n‖ ≤ C) :
    ‖(∑ n ∈ Finset.range m, d n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), d n‖
      ≤ ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * C := by
  classical
  refine le_trans (norm_weighted_sub_partialSum_le_window hH K m hm) ?_
  have hterm : ∀ n ∈ Finset.Ioc K ⌊(K : ℝ) + H⌋₊, ‖d n‖ ≤ C := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact hd n hn.1 hn.2
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

/-- The polylogarithmic coefficient bound of a triple convolution with two prime-supported factors,
transported to the smoothing error. -/
theorem norm_weighted_sub_partialSum_convolution_le {a b c : ℕ → ℂ}
    (ha : ∀ p : ℕ, a p ≠ 0 → Nat.Prime p) (haB : ∀ p : ℕ, ‖a p‖ ≤ Real.log p)
    (hb : ∀ q : ℕ, b q ≠ 0 → Nat.Prime q) (hbB : ∀ q : ℕ, ‖b q‖ ≤ Real.log q)
    (hc : ∀ k : ℕ, ‖c k‖ ≤ 1) {H : ℝ} (hH : 0 < H) (K m : ℕ)
    (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, (LSeries.convolution a (LSeries.convolution b c)) n
          * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), (LSeries.convolution a (LSeries.convolution b c)) n‖
      ≤ ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ)
          * ((Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 2) := by
  refine norm_weighted_sub_partialSum_le_uniform hH K m hm fun n hn hnle => ?_
  have hn1 : 1 ≤ n := by omega
  refine (norm_convolution_triple_le_log_pow ha haB hb hbB hc hn1).trans ?_
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  have hle : Real.log (n : ℝ) ≤ Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) := by
    refine Real.log_le_log (by linarith) ?_
    exact_mod_cast hnle
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogn hle 4) (by positivity)

/-- **The smoothing error of the Granville–Harper–Soundararajan convolution.**  For `‖f‖ ≤ 1` the
threefold convolution of the two prime weights with `f` has polylogarithmic coefficients, so the smooth
cutoff differs from the sharp one by at most the window length times `(log⌊K+H⌋)⁴/(log 2)³`. -/
theorem norm_weighted_sub_partialSum_ghs_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N M : ℕ)
    {H : ℝ} (hH : 0 < H) (K m : ℕ) (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m,
          (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f M) f)) n
            * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1),
            (LSeries.convolution (ghsOuter f N) (LSeries.convolution (ghsInner f M) f)) n‖
      ≤ ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ)
          * ((Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 3) := by
  refine norm_weighted_sub_partialSum_le_uniform hH K m hm fun n hn hnle => ?_
  have hn1 : 1 ≤ n := by omega
  refine (norm_ghsTriple_le hf N M hn1).trans ?_
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  have hle : Real.log (n : ℝ) ≤ Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) := by
    refine Real.log_le_log (by linarith) ?_
    exact_mod_cast hnle
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlogn hle 4) (by positivity)

end RHTower.Sieve
end
