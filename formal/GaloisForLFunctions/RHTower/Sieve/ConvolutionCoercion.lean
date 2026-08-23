import GaloisForLFunctions.RHTower.Sieve.VaughanBlockDecomposition

/-!
# Coercing a Dirichlet convolution to the complex antidiagonal form

The type-I and type-II estimates are stated for complex coefficient functions on the divisor
antidiagonal.  These three lemmas put the three Vaughan pieces into that form.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem coe_mul_apply (f g : ArithmeticFunction ℝ) (n : ℕ) :
    (((f * g) n : ℝ) : ℂ)
      = ∑ p ∈ n.divisorsAntidiagonal, ((f p.1 : ℝ) : ℂ) * ((g p.2 : ℝ) : ℂ) := by
  rw [ArithmeticFunction.mul_apply]
  push_cast
  rfl

theorem coe_zeta_apply_of_ne_zero {k : ℕ} (hk : k ≠ 0) :
    (((zeta : ArithmeticFunction ℝ) k : ℝ) : ℂ) = 1 := by
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hk]
  norm_num

/-- The `ζ`-convolution in complex antidiagonal form. -/
theorem coe_zeta_mul_apply' (c : ArithmeticFunction ℝ) (n : ℕ) :
    ((((zeta : ArithmeticFunction ℝ) * c) n : ℝ) : ℂ)
      = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℂ) * ((c p.2 : ℝ) : ℂ) := by
  rw [coe_mul_apply]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  have hp1 : p.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp
    exact hp.2 hp.1.symm
  rw [coe_zeta_apply_of_ne_zero hp1]

/-- The `log`-convolution in complex antidiagonal form. -/
theorem coe_log_mul_apply' (c : ArithmeticFunction ℝ) (n : ℕ) :
    (((ArithmeticFunction.log * c) n : ℝ) : ℂ)
      = ∑ p ∈ n.divisorsAntidiagonal,
          ((Real.log (p.1 : ℝ) : ℝ) : ℂ) * ((c p.2 : ℝ) : ℂ) := by
  rw [coe_mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ArithmeticFunction.log_apply]

end

end RHTower.Sieve
