import GaloisForLFunctions.RHTower.Sieve.PrimeSupportedConvolutionBound
import GaloisForLFunctions.HTGeometry.SmoothWeightWindow

/-!
# The smoothing error of the triple convolution, in closed form

The transition window `(K, ⌊K+H⌋]` carries `⌊K+H⌋ - K` terms, and every coefficient of a threefold
convolution with two prime-supported factors is at most `(log⌊K+H⌋)⁴/(log 2)²`.  So replacing the sharp
cutoff by the smooth weight costs at most the product:

`‖∑_{n<m} d(n)w(n) − ∑_{n≤K} d(n)‖ ≤ (⌊K+H⌋ − K)·(log⌊K+H⌋)⁴/(log 2)²`,   `K + H ≤ m`.

Nothing arithmetic enters: no divisor estimate, no mean value theorem in short intervals.  At
`H = K/(log K)⁶` the bound is `O(K/(log K)²)`, which is inside the error budget of the
Granville–Harper–Soundararajan argument by two logarithms.
-/

noncomputable section
namespace RHTower.Sieve
open Finset GaloisForLFunctions.HTGeometry

/-- **The smoothing error for the triple convolution, explicitly.**  The transition window has
`⌊K+H⌋ - K` terms and each coefficient is at most `(log⌊K+H⌋)⁴/(log 2)²`, so replacing the sharp cutoff
by the smooth one costs at most their product — no arithmetic input beyond the pointwise coefficient
bound. -/
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
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine le_trans (norm_weighted_sub_partialSum_le_window hH K m hm) ?_
  have hterm : ∀ n ∈ Finset.Ioc K ⌊(K : ℝ) + H⌋₊,
      ‖(LSeries.convolution a (LSeries.convolution b c)) n‖
        ≤ (Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 / (Real.log 2) ^ 2 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hbound := norm_convolution_triple_le_log_pow ha haB hb hbB hc hn1
    refine hbound.trans ?_
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
    have hle : Real.log (n : ℝ) ≤ Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hn.2
    have hpow : (Real.log (n : ℝ)) ^ 4 ≤ (Real.log ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ)) ^ 4 :=
      pow_le_pow_left₀ hlogn hle 4
    exact div_le_div_of_nonneg_right hpow (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

end RHTower.Sieve
end
