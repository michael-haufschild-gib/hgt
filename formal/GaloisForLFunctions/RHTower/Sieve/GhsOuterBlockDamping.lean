import GaloisForLFunctions.RHTower.Sieve.GhsCoefficients
/-!
# The outer weight's own damping, kept block by block

The outer weight of the Granville–Harper–Soundararajan convolution is `a_p = f(p)log p/log⌊N/p⌋`, and bounding
`1/log⌊N/p⌋` by the constant `1/log 2` — which is all a global bound can do — throws away a factor that decays
as `p` approaches `N`.  On the dyadic block `2^j ≤ p < 2^{j+1}` the denominator is at least `log⌊N/2^{j+1}⌋`, so

`‖a_p‖ ≤ (j+1)log 2/log⌊N/2^{j+1}⌋`,

and the complementary scale `⌊N/2^{j+1}⌋` is at least `2^{⌊log₂N⌋−j−1}`, whose logarithm is
`(⌊log₂N⌋ − j − 1)log 2`.  So the `j`-th block's coefficient constant is `≍ (j+1)/(log₂N − j)`: small for the
early blocks and large only for the last few, where the block itself is short.  Weighting the block sum this way
is worth a logarithm over the constant bound.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The outer weight on a dyadic block.**  Its own damping is kept: on the block `2^j ≤ p < 2^{j+1}` the
denominator `log⌊N/p⌋` is at least `log⌊N/2^{j+1}⌋`, so

`‖a_p‖ ≤ (j+1)log 2/log⌊N/2^{j+1}⌋`,

which decays as the block approaches `N` — the factor that a constant bound `1/log 2` throws away. -/
theorem norm_ghsOuter_le_block {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {j p : ℕ}
    (hjp : Nat.log 2 p = j) (h2 : 2 ≤ N / 2 ^ (j + 1)) :
    ‖ghsOuter f N p‖
      ≤ (((j : ℝ) + 1) * Real.log 2) / Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hblockR : (2 : ℝ) ≤ ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast h2
  have hden : 0 < Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hnum : (0 : ℝ) ≤ ((j : ℝ) + 1) * Real.log 2 := by positivity
  rw [ghsOuter]
  by_cases hc : Nat.Prime p ∧ 2 ≤ N / p
  · rw [if_pos hc]
    have hp2 : 2 ≤ p := hc.1.two_le
    have hppos : 0 < p := by omega
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.trans' (by norm_num)
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hpR
    -- the block's upper endpoint bounds the numerator
    have hhigh : p < 2 ^ (j + 1) := by
      rw [← hjp]
      exact Nat.lt_pow_succ_log_self (by norm_num) p
    have hupper : Real.log (p : ℝ) ≤ ((j : ℝ) + 1) * Real.log 2 := by
      have hhR : (p : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        have : ((p : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hhigh.le
        simpa using this
      have hlg := Real.log_le_log (by linarith) hhR
      rw [Real.log_pow] at hlg
      calc Real.log (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * Real.log 2 := hlg
        _ = ((j : ℝ) + 1) * Real.log 2 := by push_cast; ring
    -- the block's upper endpoint bounds the denominator from below
    have hdivle : N / 2 ^ (j + 1) ≤ N / p := Nat.div_le_div_left hhigh.le hppos
    have hdenle : Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) ≤ Real.log ((N / p : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      exact_mod_cast hdivle
    have hratio : Real.log (p : ℝ) / Real.log ((N / p : ℕ) : ℝ)
        ≤ (((j : ℝ) + 1) * Real.log 2) / Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) :=
      div_le_div₀ hnum hupper hden hdenle
    have hrnn : (0 : ℝ) ≤ Real.log p / Real.log ((N / p : ℕ) : ℝ) :=
      div_nonneg hlogp (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnn]
    calc ‖f p‖ * (Real.log p / Real.log ((N / p : ℕ) : ℝ))
        ≤ 1 * (Real.log p / Real.log ((N / p : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (hf p) hrnn
      _ = Real.log p / Real.log ((N / p : ℕ) : ℝ) := one_mul _
      _ ≤ (((j : ℝ) + 1) * Real.log 2) / Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := hratio
  · rw [if_neg hc, norm_zero]
    positivity

/-- The block's complementary scale is at least `2^{⌊log₂N⌋ − j − 1}`, so its logarithm is at least
`(⌊log₂N⌋ − j − 1)·log 2`: the outer weight's damping on the `j`-th block is `≍ (j+1)/(log₂N − j)`. -/
theorem log_div_block_ge {N j : ℕ} (hj : j + 1 ≤ Nat.log 2 N) :
    ((Nat.log 2 N : ℝ) - (j : ℝ) - 1) * Real.log 2
      ≤ Real.log ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
  have hlow : (2 : ℕ) ^ (Nat.log 2 N - (j + 1)) ≤ N / 2 ^ (j + 1) := by
    have hNpow : (2 : ℕ) ^ Nat.log 2 N ≤ N := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp at hj
      · exact Nat.pow_log_le_self 2 (by omega)
    have hsplit : (2 : ℕ) ^ (Nat.log 2 N - (j + 1)) = 2 ^ Nat.log 2 N / 2 ^ (j + 1) := by
      rw [Nat.pow_div hj (by norm_num)]
    rw [hsplit]
    exact Nat.div_le_div_right hNpow
  have hlowR : ((2 : ℝ) ^ (Nat.log 2 N - (j + 1) : ℕ)) ≤ ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
    have : ((2 ^ (Nat.log 2 N - (j + 1)) : ℕ) : ℝ) ≤ ((N / 2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast hlow
    simpa using this
  have hlg := Real.log_le_log (by positivity) hlowR
  rw [Real.log_pow] at hlg
  refine le_trans (le_of_eq ?_) hlg
  have hcast : ((Nat.log 2 N - (j + 1) : ℕ) : ℝ) = (Nat.log 2 N : ℝ) - (j : ℝ) - 1 := by
    have h : (j + 1) ≤ Nat.log 2 N := hj
    push_cast [Nat.cast_sub h]
    ring
  rw [hcast]

end RHTower.Sieve
end
