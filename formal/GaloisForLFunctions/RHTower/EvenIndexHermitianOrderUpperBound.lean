import GaloisForLFunctions.RHTower.EvenIndexHermitianAbelBound
import GaloisForLFunctions.HTGeometry.LogOrderLimsupBound
open Complex Filter
open scoped BigOperators

/-!
# Order upper bound for the even-index Hermitian mixed convolution power

For a unit-bounded coefficient sequence, the `2k`-fold Hermitian mixed additive convolution power
grows at most polynomially: `‖R_{k}(N)‖ ≤ (N+1)^{2k-1}` (the composition count).  Hence its even-index
order exponent `Ψ = limsup log(1 + max(Re R_k(N), 0)) / log(N+1)` is at most `2k-1`
(`limsup_log_mixedAdditiveConvolutionPower_re_le`) — the upper half of the raw-Möbius order law `(R3)`.
The bound reuses the corpus convolution-power estimate and the log-order limsup capstone
`HTGeometry.limsup_log_one_add_div_log_le`.
-/

namespace RHTower

theorem norm_additiveConvolutionPower_succ_le_pow {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (j N : ℕ) :
    ‖additiveConvolutionPower a (j + 1) N‖ ≤ ((N : ℝ) + 1) ^ j := by
  have h := norm_additiveConvolutionPower_succ_le a (A := 1) (α := 0) (by norm_num) le_rfl
    (fun N => by simpa using ha N) j N
  simpa [Real.rpow_natCast] using h

theorem norm_mixedAdditiveConvolutionPower_le_pow {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (j N : ℕ) :
    ‖mixedAdditiveConvolutionPower a (j + 1) N‖ ≤ ((N : ℝ) + 1) ^ (2 * j + 1) := by
  show ‖∑ ab ∈ Finset.antidiagonal N, additiveConvolutionPower a (j + 1) ab.1 *
    (starRingEnd ℂ) (additiveConvolutionPower a (j + 1) ab.2)‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  have hstep : ∀ ab ∈ Finset.antidiagonal N,
      ‖additiveConvolutionPower a (j + 1) ab.1 *
          (starRingEnd ℂ) (additiveConvolutionPower a (j + 1) ab.2)‖ ≤ ((N : ℝ) + 1) ^ (2 * j) := by
    intro ab hab
    rw [Finset.mem_antidiagonal] at hab
    rw [norm_mul, RCLike.norm_conj]
    have hb1 : ((ab.1 : ℝ) + 1) ^ j ≤ ((N : ℝ) + 1) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      have h : (ab.1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ab.1 ≤ N)
      linarith
    have hb2 : ((ab.2 : ℝ) + 1) ^ j ≤ ((N : ℝ) + 1) ^ j := by
      apply pow_le_pow_left₀ (by positivity)
      have h : (ab.2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : ab.2 ≤ N)
      linarith
    calc ‖additiveConvolutionPower a (j + 1) ab.1‖ * ‖additiveConvolutionPower a (j + 1) ab.2‖
        ≤ ((N : ℝ) + 1) ^ j * ((N : ℝ) + 1) ^ j :=
          mul_le_mul ((norm_additiveConvolutionPower_succ_le_pow ha j ab.1).trans hb1)
            ((norm_additiveConvolutionPower_succ_le_pow ha j ab.2).trans hb2) (norm_nonneg _)
            (by positivity)
      _ = ((N : ℝ) + 1) ^ (2 * j) := by rw [← pow_add, ← two_mul]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  refine le_of_eq ?_
  push_cast
  rw [pow_succ]
  ring

/-- **Order upper bound (R3).**  For a unit-bounded coefficient sequence, the even-index order
exponent of the Hermitian mixed additive convolution power is at most `2j+1`: the limsup of
`log(1 + max(Re R_{j+1}(N), 0)) / log(N+1)` is bounded by the degree of the composition count. -/
theorem limsup_log_mixedAdditiveConvolutionPower_re_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (j : ℕ) :
    Filter.limsup (fun N => Real.log (1 + max (mixedAdditiveConvolutionPower a (j + 1) N).re 0)
      / Real.log ((N : ℝ) + 1)) Filter.atTop ≤ ((2 * j + 1 : ℕ) : ℝ) :=
  GaloisForLFunctions.HTGeometry.limsup_log_one_add_div_log_le (C := 1) one_pos
    (fun N => le_max_right _ _)
    (fun N => max_le
      ((Complex.re_le_norm _).trans (by
        simpa using norm_mixedAdditiveConvolutionPower_le_pow ha j N))
      (by positivity))

end RHTower
