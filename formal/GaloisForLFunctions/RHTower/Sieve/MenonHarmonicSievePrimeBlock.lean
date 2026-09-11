import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSieveSwappedCanonical

/-!
# The two-dimensional sieve's mean square, in the ladder's own prime-block language

`Sieve/DyadicPrimeMeanSquare` states its bound for `logPoly (fun n => 1/n) (bigPrimeSet R (2R))`,
the *unsigned* harmonic prime polynomial.  The harmonic Ramare ladder works with
`harmonicPrimeBlockPoly`, which carries the Moebius sign.  On a set of primes the two differ by an
overall sign, because `mu(p) = -1`; so the sieve's mean square transfers verbatim, and the swapped
receiver of `MenonHarmonicRamareBlockSwapped` can consume it in place of reciprocal
Halasz--Montgomery.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- On a set of primes the harmonic prime block polynomial is minus the unsigned one. -/
theorem harmonicPrimeBlockPoly_eq_neg_logPoly_of_prime {B : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) (w : ℝ) :
    harmonicPrimeBlockPoly B w = -logPoly (fun n => ((1 : ℂ) / (n : ℂ))) B w := by
  rw [harmonicPrimeBlockPoly, logPoly, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [harmonicMoebiusPhase, moebiusPhase, ArithmeticFunction.moebius_apply_prime (hB p hp),
    unitLogPhase]
  push_cast
  ring

/-- Hence the two have the same norm at every frequency. -/
theorem norm_harmonicPrimeBlockPoly_eq_of_prime {B : Finset ℕ}
    (hB : ∀ p ∈ B, p.Prime) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B w‖ = ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) B w‖ := by
  rw [harmonicPrimeBlockPoly_eq_neg_logPoly_of_prime hB, norm_neg]

/-- **The two-dimensional sieve's mean square for the ladder's own prime block.** -/
theorem integral_Icc_normSq_harmonicPrimeBlockPoly_bigPrimeSet_le_canonical
    {R h P₁ : ℕ} {W : ℝ}
    (hW : 1 ≤ W) (hhR : h ≤ R) (hR1 : 1 ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) :
    (∫ w in Set.Icc (-W) W,
        ‖harmonicPrimeBlockPoly (bigPrimeSet R (2 * R)) w‖ ^ 2)
      ≤ (5 / (4 * sieveSwappedDelta W)) * (1 / (R : ℝ) ^ 2)
          * (((bigPrimeSet R (2 * R)).card : ℝ)
            + 2 * (2 * Real.exp 1 * ((sieveSwappedBudget R W : ℕ) : ℝ) * (2 * (R : ℝ))
                    / (Real.exp (mertensS h - mertensS P₁)) ^ 2
                  + ((sieveSwappedBudget R W : ℕ) : ℝ) *
                      ∑ e ∈ (rangePrimorial P₁ h).divisors,
                      (if ((e : ℕ) : ℝ) ≤ sieveSwappedLevel P₁ h
                        then 2 * 6 ^ e.primeFactors.card else 0))) := by
  have hcanon := integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le_canonical
    (P := (∅ : Finset ℕ)) (D := (∅ : Finset ℕ)) (R := R) (h := h) (P₁ := P₁) (W := W)
    hW hhR hR1 hP₁ hP₁h hh1
  have hrw : (∫ w in Set.Icc (-W) W,
      ‖harmonicPrimeBlockPoly (bigPrimeSet R (2 * R)) w‖ ^ 2)
      = ∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) (bigPrimeSet R (2 * R)) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [norm_harmonicPrimeBlockPoly_eq_of_prime (fun p hp => prime_of_mem_bigPrimeSet hp)]
  rw [hrw]
  have hδ0 : 0 < sieveSwappedDelta W := by
    have hpi : (0 : ℝ) < 2 * Real.pi * W := by nlinarith [Real.pi_gt_three]
    rw [sieveSwappedDelta]; positivity
  have hR0 : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR1
  have hsieve := integral_normSq_dyadicPrimePoly_le (R := R) (h := h)
    (K := sieveSwappedBudget R W) (k := sieveSwappedDimension P₁ h)
    (P₁ := P₁) (δ := sieveSwappedDelta W) (W := W) (z := sieveSwappedLevel P₁ h)
    hδ0
    (by
      rw [sieveSwappedDelta, div_le_one (by nlinarith [Real.pi_gt_three])]
      nlinarith [Real.pi_gt_three])
    (by
      rw [sieveSwappedDelta,
        show 2 * Real.pi * (1 / (2 * Real.pi * W)) * W
          = (2 * Real.pi * W) / (2 * Real.pi * W) by field_simp,
        div_self (by nlinarith [Real.pi_gt_three] : (2 * Real.pi * W) ≠ 0)])
    (by rw [sieveSwappedBudget]; exact Nat.le_ceil _)
    hhR hR1 hP₁ hP₁h hh1
    (by
      rw [sieveSwappedLevel]
      exact one_le_pow₀ (by exact_mod_cast hh1))
    (le_of_eq rfl)
    (by rw [sieveSwappedDimension]; exact Nat.le_ceil _)
  exact hsieve

end

end RHTower.Sieve
