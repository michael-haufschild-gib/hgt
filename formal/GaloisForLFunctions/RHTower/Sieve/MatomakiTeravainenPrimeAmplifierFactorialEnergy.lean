import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierEnergy
import GaloisForLFunctions.RHTower.Sieve.PrimePowerFactorialEnergy

/-!
# Sharp factorial energy for the Matomäki--Teräväinen prime amplifier

Unique factorization identifies each coefficient fibre with permutations of one prime multiset.
The resulting loss is `ell!`, improving the generic `ell ^ ell` loss while retaining the paper's
source-scale consequence.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Every coefficient of the unraised prime indicator has norm at most one. -/
theorem norm_mtTypeIPrimeCoeff_le_one (P : ℕ) (j : Fin (2 * P)) :
    ‖mtTypeIPrimeCoeff P j‖ ≤ 1 := by
  rw [mtTypeIPrimeCoeff]
  split <;> simp

/-- Pointwise factorial bound for every complete powered-prime coefficient. -/
theorem norm_convPow_mtTypeIPrimeCoeff_le_factorial
    (P ell : ℕ) (j : Fin ((2 * P) ^ ell)) :
    ‖convPow (2 * P) ell (mtTypeIPrimeCoeff P) j‖ ≤ (ell.factorial : ℝ) :=
  norm_convPow_le_factorial_of_prime_support
    (2 * P) ell (mtTypeIPrimeCoeff P) (mtTypeIPrimeCoeff_prime_support P)
      (norm_mtTypeIPrimeCoeff_le_one P) j

/-- Pointwise factorial bound after extension to arbitrary positive anchors. -/
theorem norm_mtTypeIPrimeRaisedCoeff_le_factorial
    (P ell m : ℕ) :
    ‖mtTypeIPrimeRaisedCoeff P ell m‖ ≤ (ell.factorial : ℝ) := by
  rw [mtTypeIPrimeRaisedCoeff, anchoredCoeff]
  split
  · exact norm_convPow_mtTypeIPrimeCoeff_le_factorial P ell _
  · simp

/-- Complete coefficient energy of the powered prime amplifier with the sharp factorial loss. -/
theorem sum_normSq_mtTypeIPrimeRaisedCoeff_le_factorial (P ell : ℕ) :
    ∑ j : Fin ((2 * P) ^ ell),
        ‖convPow (2 * P) ell (mtTypeIPrimeCoeff P) j‖ ^ 2 ≤
      (ell.factorial : ℝ) * (P : ℝ) ^ ell := by
  have hraw := primePowerSupportSum_normSq_convPow_le_factorial
    (2 * P) ell (mtTypeIPrimeCoeff P) (mtTypeIPrimeCoeff_prime_support P)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => sq_nonneg _)
      (sum_normSq_mtTypeIPrimeCoeff_le P) ell) (by positivity))

/-- Every exact Watt block inherits the sharp complete factorial energy bound. -/
theorem sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le_factorial (P ell B : ℕ) :
    ∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
      (ell.factorial : ℝ) * (P : ℝ) ^ ell := by
  have hsubset : Finset.Ioc B (2 * B) ⊆ Finset.Ico (B + 1) (2 * (B + 1)) := by
    intro m hm
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hm ⊢
    omega
  have hcut :
      (∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) ≤
        ∑ m ∈ Finset.Ico (B + 1) (2 * (B + 1)),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => sq_nonneg _)
  have hfull := sum_normSq_anchoredCoeff_Ico_le ((2 * P) ^ ell) (B + 1)
    (convPow (2 * P) ell (mtTypeIPrimeCoeff P))
  exact hcut.trans (by
    simpa [mtTypeIPrimeRaisedCoeff] using
      (hfull.trans (sum_normSq_mtTypeIPrimeRaisedCoeff_le_factorial P ell)))

/-- The sharp factorial loss is no larger than the previous `ell ^ ell` loss. -/
theorem mtTypeIPrimeRaisedCoeff_factorial_energy_le_power (P ell : ℕ) :
    (ell.factorial : ℝ) * (P : ℝ) ^ ell ≤
      (ell : ℝ) ^ ell * (P : ℝ) ^ ell := by
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.factorial_le_pow ell

/-- Source-scale form retained with the sharper factorial intermediate bound. -/
theorem sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_factorial_le_rpow
    {P ell B : ℕ} {rho : ℝ} (hP : 1 ≤ P)
    (hell : (ell : ℝ) ≤ (P : ℝ) ^ rho) :
    ∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
      (((P ^ ell : ℕ) : ℝ)) ^ (1 + rho) :=
  (sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le_factorial P ell B).trans
    ((mtTypeIPrimeRaisedCoeff_factorial_energy_le_power P ell).trans
      (mtTypeIPrimeRaisedCoeff_energy_absorb hP hell))

end

end RHTower.Sieve
