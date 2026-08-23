import GaloisForLFunctions.RHTower.Sieve.VonMangoldtBlockEstimate
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The coefficient energies of the type-II form

The long side is bounded by `Λ`, so its energy is at most `log L` times Chebyshev's `ψ(L)`, hence
`≪ L log L`.  The short side is bounded by `1 + d(m)`, whose second moment is the divisor moment.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The long-side coefficient energy.** -/
theorem exists_sum_typeIILong_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (U L : ℕ), 1 ≤ L →
      (∑ d ∈ Finset.Ico 1 (L + 1), ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2)
        ≤ C * (L : ℝ) * Real.log (L : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_chebyshevPsiReal_le_linear
  refine ⟨C, hC0, ?_⟩
  intro U L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hlogL : (0 : ℝ) ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  rw [Finset.Ico_add_one_right_eq_Icc]
  have hstep : ∀ d ∈ Finset.Icc 1 L,
      ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2 ≤ Real.log (L : ℝ) * vonMangoldt d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hnorm : ‖((typeIILong U d : ℝ) : ℂ)‖ = |typeIILong U d| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have h1 : |typeIILong U d| ≤ vonMangoldt d := abs_vonMangoldt_sub_truncAF_le U d
    have h2 : vonMangoldt d ≤ Real.log (d : ℝ) := ArithmeticFunction.vonMangoldt_le_log
    have h3 : Real.log (d : ℝ) ≤ Real.log (L : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast hd.1
      · exact_mod_cast hd.2
    have h0 : (0 : ℝ) ≤ |typeIILong U d| := abs_nonneg _
    nlinarith [h1, h2, h3, h0, ArithmeticFunction.vonMangoldt_nonneg (n := d)]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hpsi : (∑ d ∈ Finset.Icc 1 L, vonMangoldt d) = chebyshevPsiReal (L : ℝ) := by
    rw [chebyshevPsiReal_eq_sum_range, Nat.floor_natCast,
      sum_range_succ_vonMangoldt_eq_sum_Icc]
  rw [hpsi]
  have hle := hC (L : ℝ) hL1
  nlinarith [hle, hlogL, chebyshevPsiReal_nonneg (L : ℝ)]

/-- **The short-side coefficient energy.** -/
theorem sum_typeIIShort_sq_le (V L : ℕ) :
    (∑ m ∈ Finset.Icc 1 L, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ 2)
      ≤ 2 * (L : ℝ) + 2 * ((L : ℝ) * invSum L ^ 3) := by
  have hstep : ∀ m ∈ Finset.Icc 1 L,
      ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ 2 ≤ 2 + 2 * ((m.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro m _
    have hnorm : ‖((typeIIShort V m : ℝ) : ℂ)‖ = |typeIIShort V m| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    have h1 : |typeIIShort V m| ≤ 1 + ((m.divisors.card : ℕ) : ℝ) :=
      abs_one_sub_zeta_mul_moebius_le V m
    have h0 : (0 : ℝ) ≤ |typeIIShort V m| := abs_nonneg _
    have hd0 : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, h0, hd0, sq_nonneg (1 - ((m.divisors.card : ℕ) : ℝ))]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ← Finset.mul_sum]
  have hdiv := sum_card_divisors_sq_le L
  have hcast : ((L + 1 - 1 : ℕ) : ℝ) = (L : ℝ) := by push_cast; ring
  rw [hcast]
  linarith [hdiv]

end

end RHTower.Sieve
