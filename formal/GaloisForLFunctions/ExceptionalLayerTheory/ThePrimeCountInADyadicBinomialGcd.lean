import GaloisForLFunctions.ExceptionalLayerTheory.CommonCarriesOfDyadicCentralBinomialCoefficients
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimePowerTowerCollapse
import Mathlib.NumberTheory.Chebyshev

/-!
# The prime count in a gcd of dyadic binomial coefficients

The logarithm of the gcd exceeds the Mangoldt mass of its quotient class by
at most the total mass of higher prime powers. In particular the error is of
square-root order with a constant independent of the number of binomials.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Prime powers whose quotient has every prescribed low binary digit set. -/
def dyadicCommonPrimeMass (j N : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 (2^(j+1)*N), (dyadicQuotientCarry j N m : ℝ)*vonMangoldt m

/-- Number of powers of a prime on which every binomial carries. -/
abbrev dyadicCommonCarryLevels (j N p : ℕ) :=
  ∑ e ∈ Icc 1 (p.log (2^(j+1)*N)), dyadicQuotientCarry j N (p^e)

/-- Prime-first decomposition of the selected Mangoldt mass. -/
theorem dyadicCommonPrimeMass_eq_sum_levels (j N : ℕ) :
    dyadicCommonPrimeMass j N =
      ∑ p ∈ Nat.primesLE (2^(j+1)*N), (dyadicCommonCarryLevels j N p : ℝ)*Real.log p := by
  let X := 2^(j+1)*N
  let f := fun m : ℕ => (dyadicQuotientCarry j N m : ℝ)*vonMangoldt m
  change (∑ m ∈ Icc 1 X, f m) = _
  calc
    _ = ∑ m ∈ (Icc 1 X).filter IsPrimePow, f m := by
      symm
      refine sum_subset (filter_subset ..) fun m hm h => ?_
      have hz := vonMangoldt_eq_zero_iff.mpr (fun hp => h (mem_filter.mpr ⟨hm,hp⟩))
      simp only [f,hz,mul_zero]
    _ = _ := by
      rw [_root_.RHTower.sum_primePow_Icc_eq_sum_primesLE]
      refine sum_congr rfl fun p hp => ?_
      simp only [dyadicCommonCarryLevels,Nat.cast_sum,sum_mul]
      refine sum_congr rfl fun e he => ?_
      dsimp only [f]
      rw [vonMangoldt_apply_pow (by have := (mem_Icc.mp he).1; omega),
        vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]

private theorem gcd_dvd_top_lcm (j N : ℕ) :
    dyadicBinomialGcd j N ∣ Nat.lcmUpto (2^(j+1)*N) := by
  have hd : dyadicBinomialGcd j N ∣ Nat.centralBinom (2^j*N) := by
    cases j with
    | zero => simp [dyadicBinomialGcd]
    | succ j => exact Nat.gcd_dvd_right _ _
  apply hd.trans
  rw [Nat.centralBinom_eq_two_mul_choose,pow_succ,mul_comm (2^j) 2,mul_assoc]
  exact Chebyshev.choose_dvd_lcmUpto (by omega)

/-- The first binomial confines the prime support of the gcd below the top cutoff. -/
theorem log_dyadicBinomialGcd_eq_sum_primes (j N : ℕ) :
    Real.log (dyadicBinomialGcd j N) =
      ∑ p ∈ Nat.primesLE (2^(j+1)*N), ((dyadicBinomialGcd j N).factorization p : ℝ)*Real.log p := by
  rw [Real.log_nat_eq_sum_factorization,Finsupp.sum]
  apply sum_subset
  · rw [Nat.support_factorization,← Nat.primeFactors_lcmUpto]
    exact Nat.primeFactors_mono (gcd_dvd_top_lcm j N) (Nat.lcmUpto_ne_zero _)
  · intro p _ hp
    rw [Finsupp.mem_support_iff,not_not] at hp
    rw [hp,Nat.cast_zero,zero_mul]

/-- Positive multiplicity excess is bounded by the logarithmic mass of higher prime powers. -/
theorem dyadicBinomialGcd_log_excess_bounds (j N : ℕ) :
    0 ≤ Real.log (dyadicBinomialGcd j N) - dyadicCommonPrimeMass j N ∧
    Real.log (dyadicBinomialGcd j N) - dyadicCommonPrimeMass j N ≤
      Chebyshev.psi (2^(j+1)*N : ℕ) - Chebyshev.theta (2^(j+1)*N : ℕ) := by
  let X := 2^(j+1)*N
  let V := fun p => (dyadicBinomialGcd j N).factorization p
  have hval {p : ℕ} (hp : p ∈ Nat.primesLE X) :
      dyadicCommonCarryLevels j N p ≤ V p ∧ V p + 1 ≤ dyadicCommonCarryLevels j N p + p.log X := by
    obtain ⟨hXp,hP⟩ := Nat.mem_primesLE.mp hp
    have hL : 1 ≤ p.log X := Nat.le_log_of_pow_le hP.one_lt (by simpa using hXp)
    have hI := Ico_add_one_right_eq_Icc 1 (p.log X)
    obtain ⟨hl,hu⟩ := dyadicBinomialGcd_carry_bounds j N hP (by omega : 2 ≤ p.log X+1)
      (Nat.lt_succ_self (p.log X))
    rw [hI] at hl
    have hfirst : dyadicQuotientCarry j N p ≤ dyadicCommonCarryLevels j N p := by
      simpa only [pow_one] using (single_le_sum (f := fun e => dyadicQuotientCarry j N (p^e))
        (fun _ _ => Nat.zero_le _) (mem_Icc.mpr ⟨le_rfl,hL⟩))
    exact ⟨hl,show (dyadicBinomialGcd j N).factorization p + 1 ≤ _ by omega⟩
  rw [log_dyadicBinomialGcd_eq_sum_primes,dyadicCommonPrimeMass_eq_sum_levels,Chebyshev.psi_eq_sum_mul_log_prime,Chebyshev.theta_eq_sum_primesLE_log]
  constructor
  · apply sub_nonneg.mpr
    exact sum_le_sum fun p hp => mul_le_mul_of_nonneg_right (by exact_mod_cast (hval hp).1)
      (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
  · rw [← sum_sub_distrib,← sum_sub_distrib]
    refine sum_le_sum fun p hp => ?_
    have hc : (V p : ℝ)+1 ≤ (dyadicCommonCarryLevels j N p : ℝ) + (p.log X : ℝ) := by exact_mod_cast (hval hp).2
    have hg := mul_le_mul_of_nonneg_right hc
      (Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
    change (V p : ℝ)*Real.log p - (dyadicCommonCarryLevels j N p : ℝ)*Real.log p ≤ (p.log X : ℝ)*Real.log p - Real.log p
    linarith only [hg]

/-- One absolute constant works at every dyadic depth and every cutoff. -/
theorem exists_uniform_dyadicBinomialGcd_log_error :
    ∃ C : ℝ, ∀ j N : ℕ,
      |Real.log (dyadicBinomialGcd j N) - dyadicCommonPrimeMass j N| ≤
        C * Real.sqrt (2^(j+1)*N : ℕ) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C,fun j N => ?_⟩
  obtain ⟨h₀,h₁⟩ := dyadicBinomialGcd_log_excess_bounds j N
  rw [abs_of_nonneg h₀]
  exact h₁.trans (hC _)

#print axioms dyadicBinomialGcd_log_excess_bounds
#print axioms exists_uniform_dyadicBinomialGcd_log_error

end GaloisForLFunctions.ExceptionalLayerTheory
