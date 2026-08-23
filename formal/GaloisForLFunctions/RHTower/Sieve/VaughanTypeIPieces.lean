import GaloisForLFunctions.RHTower.Sieve.ConvolutionCoercion
import GaloisForLFunctions.RHTower.Sieve.LogConvolutionTypeI

/-!
# Coefficient bounds for the type-I pieces of Vaughan's identity

The coefficients of `ζ ∗ (Λ_U ∗ μ_V)` and of `log ∗ μ_V` are bounded by `log b` and by `1`.  Both
follow from `Λ ∗ ζ = log` and from `μ ∈ {−1, 0, 1}`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem zeta_real_apply_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    ((zeta : ArithmeticFunction ℝ) k : ℝ) = 1 := by
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hk]
  norm_num

/-- The truncated Möbius coefficients are bounded by one. -/
theorem abs_truncAF_moebius_le_one (V b : ℕ) :
    |truncAF (moebius : ArithmeticFunction ℝ) V b| ≤ 1 := by
  rw [truncAF_apply]
  split_ifs with h
  · rw [ArithmeticFunction.intCoe_apply]
    by_cases hm : moebius b = 0
    · simp [hm]
    · rcases ArithmeticFunction.moebius_ne_zero_iff_eq_or.1 hm with h1 | h1 <;> simp [h1]
  · norm_num

/-- The truncated von Mangoldt / Möbius convolution is bounded by the logarithm. -/
theorem abs_truncAF_conv_le_log (U V b : ℕ) :
    |(truncAF vonMangoldt U * truncAF (moebius : ArithmeticFunction ℝ) V) b|
      ≤ Real.log b := by
  rw [ArithmeticFunction.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hstep : ∀ p ∈ b.divisorsAntidiagonal,
      |truncAF vonMangoldt U p.1 * truncAF (moebius : ArithmeticFunction ℝ) V p.2|
        ≤ vonMangoldt p.1 := by
    intro p _
    rw [abs_mul]
    have h1 : |truncAF vonMangoldt U p.1| ≤ vonMangoldt p.1 := by
      rw [truncAF_apply]
      split_ifs
      · rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      · simp [ArithmeticFunction.vonMangoldt_nonneg]
    have h2 := abs_truncAF_moebius_le_one V p.2
    have h3 : (0 : ℝ) ≤ |truncAF vonMangoldt U p.1| := abs_nonneg _
    nlinarith [h1, h2, h3]
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  have hzeta : ((vonMangoldt : ArithmeticFunction ℝ) * (zeta : ArithmeticFunction ℝ)) b
      = ArithmeticFunction.log b := by rw [vonMangoldt_mul_zeta]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply] at hzeta
  rw [← hzeta]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hp2 : p.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp
    exact hp.2 hp.1.symm
  rw [zeta_real_apply_of_ne_zero hp2, mul_one]

end

end RHTower.Sieve
