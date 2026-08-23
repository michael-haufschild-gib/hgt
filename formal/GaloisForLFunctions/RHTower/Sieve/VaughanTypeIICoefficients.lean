import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIEstimates
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareMoment

/-!
# Coefficient bounds for the type-II piece of Vaughan's identity

The type-II bilinear form has `Λ − Λ_U` on one side and `1 − ζ ∗ μ_V` on the other.  The first is
supported above `U` and bounded by `Λ`; the second is supported above `V` and bounded by
`1 + d(m)`, whose second moment is the divisor moment of `DivisorSquareMoment.lean`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem card_divisorsAntidiagonal (n : ℕ) : n.divisorsAntidiagonal.card = n.divisors.card := by
  rw [← Nat.map_div_right_divisors]
  simp

/-- The long-side coefficients vanish below the truncation. -/
theorem vonMangoldt_sub_truncAF_eq_zero {U k : ℕ} (hk : k ≤ U) :
    (vonMangoldt - truncAF vonMangoldt U) k = 0 := by
  have hsub : (vonMangoldt - truncAF vonMangoldt U) k
      = vonMangoldt k - truncAF vonMangoldt U k := rfl
  rw [hsub, truncAF_apply, if_pos hk, sub_self]

/-- The long-side coefficients are bounded by `Λ`. -/
theorem abs_vonMangoldt_sub_truncAF_le (U k : ℕ) :
    |(vonMangoldt - truncAF vonMangoldt U) k| ≤ vonMangoldt k := by
  have hsub : (vonMangoldt - truncAF vonMangoldt U) k
      = vonMangoldt k - truncAF vonMangoldt U k := rfl
  rw [hsub, truncAF_apply]
  split_ifs
  · simp [ArithmeticFunction.vonMangoldt_nonneg]
  · rw [sub_zero, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The short-side coefficients are bounded by `1 + d(m)`. -/
theorem abs_one_sub_zeta_mul_moebius_le (V m : ℕ) :
    |((1 : ArithmeticFunction ℝ) - (zeta : ArithmeticFunction ℝ)
        * truncAF (moebius : ArithmeticFunction ℝ) V) m|
      ≤ 1 + (m.divisors.card : ℝ) := by
  have hsub : ((1 : ArithmeticFunction ℝ) - (zeta : ArithmeticFunction ℝ)
      * truncAF (moebius : ArithmeticFunction ℝ) V) m
      = (1 : ArithmeticFunction ℝ) m
        - ((zeta : ArithmeticFunction ℝ) * truncAF (moebius : ArithmeticFunction ℝ) V) m := rfl
  rw [hsub]
  have h1 : |(1 : ArithmeticFunction ℝ) m| ≤ 1 := by
    rw [ArithmeticFunction.one_apply]
    split_ifs <;> norm_num
  have h2 : |((zeta : ArithmeticFunction ℝ)
      * truncAF (moebius : ArithmeticFunction ℝ) V) m| ≤ (m.divisors.card : ℝ) := by
    rw [ArithmeticFunction.mul_apply]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ p ∈ m.divisorsAntidiagonal,
        |(zeta : ArithmeticFunction ℝ) p.1
          * truncAF (moebius : ArithmeticFunction ℝ) V p.2| ≤ 1 := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      have hp1 : p.1 ≠ 0 := by
        intro h
        rw [h, zero_mul] at hp
        exact hp.2 hp.1.symm
      rw [abs_mul, zeta_real_apply_of_ne_zero hp1, abs_one, one_mul]
      exact abs_truncAF_moebius_le_one V p.2
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_divisorsAntidiagonal]
  exact le_trans (abs_sub _ _) (by linarith)

end

end RHTower.Sieve
