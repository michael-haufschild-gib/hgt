import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff

/-!
# Explicit constants for rough harmonic conditioning

The finite-sieve ground moment bounds the reciprocal Euler product without an
asymptotic threshold. Thin-shell estimates then give an explicit uniform
prime-fibre variance constant and an explicit conditioning error.
-/

noncomputable section

open Finset Filter
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open HTGeometry

/-- The prime-prefix sieve density is the usual finite Mertens product. -/
theorem sieveDensity_primePrefix_succ (n : ℕ) :
    sieveDensity (primePrefixSieve (n + 1)) = RHTower.mertensPrimeProduct n := by
  unfold sieveDensity primePrefixSieve RHTower.mertensPrimeProduct
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => 1 - (p : ℝ)⁻¹)
    (fun p hp => (mem_filter.mp hp).2), prod_filter]
  congr 1
  ext k
  simp only [mem_range, mem_Icc, Nat.zero_le, true_and]
  omega

/-- The Euler correction gives the numerical bound `P(n) log n ≥ 1/128`. -/
theorem mertensPrimeProduct_mul_log_ge_one_div_128 {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / 128 ≤ RHTower.mertensPrimeProduct n * Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith only [h]
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hnext : Real.log (n + 1 : ℕ) ≤ Real.log n + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ))
      (show ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * 2 by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
        push_cast
        linarith only [hn1])
    rwa [Real.log_mul hn0.ne' (by norm_num)] at h
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hL := ladderConstant_le_log (show 1 ≤ n + 1 by omega)
  have hfactor : Real.log 2 + 2 * ladderConstant (n + 1) + 4 ≤ 64 * Real.log n := by
    rw [hlog4] at hL
    linarith only [hL, hnext, hlogn, hlog2]
  have hmass := sievedHarmonic_le_density_log_euler (primePrefixSieve (n + 1)) 1
  rw [sievedHarmonic_primePrefix_eq, sieveDensity_primePrefix_succ,
    sieveEuler_primePrefix_sub_euler] at hmass
  have hone : roughHarmonic (n + 1) 1 = 1 := by
    simp [roughHarmonic, roughInterval]
  rw [hone] at hmass
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hmass
  have hprod := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ 2 * RHTower.mertensPrimeProduct n by
      exact mul_nonneg zero_le_two (RHTower.mertensPrimeProduct_pos n).le)
  nlinarith only [hmass, hprod]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.mertensPrimeProduct_mul_log_ge_one_div_128
