import GaloisForLFunctions.ArithmeticIndexDescent.AllHigherPrimePowerMixedTailsAreGammaSmall
import GaloisForLFunctions.RHTower.RandomEulerAbscissa

/-!
# The exact absolute-coefficient threshold for critical Euler powers

The coefficient tail over all primes, beginning at exponent `r + 1`, is
summable exactly when `r ≥ 2`. Cubes and higher powers therefore have one
finite absolute coefficient budget. Prime and square coefficients do not.
This concerns coefficient mass, not convergence of correlations on compact
sources or cancellation with the polar contribution.
-/

noncomputable section
open RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open ArithmeticIndexDescent

/-- Literal critical Euler weights for all powers starting at exponent `r + 1`. -/
def criticalEulerTailWeight (r : ℕ) (pk : Nat.Primes × ℕ) : ℝ :=
  2 * xiMassPrimePowerCriticalWeight pk.1 (pk.2 + r)

/-- The coefficient is the actual von Mangoldt weight, with no damping factor. -/
theorem criticalEulerTailWeight_eq (r : ℕ) (pk : Nat.Primes × ℕ) :
    criticalEulerTailWeight r pk =
      2 * ArithmeticFunction.vonMangoldt ((pk.1 : ℕ) ^ (pk.2 + r + 1)) /
        Real.sqrt (((pk.1 : ℕ) ^ (pk.2 + r + 1) : ℕ) : ℝ) :=
  (primePower_coefficient_eq_twice_criticalWeight pk.1 (pk.2 + r)).symm

theorem criticalEulerTailWeight_nonneg (r : ℕ) (pk : Nat.Primes × ℕ) :
    0 ≤ criticalEulerTailWeight r pk :=
  mul_nonneg (by norm_num) (norm_nonneg _)

/-- Every later exponent tail is a subseries of the complete cube-and-higher family. -/
theorem summable_criticalEulerTailWeight_of_two_le {r : ℕ} (hr : 2 ≤ r) :
    Summable (criticalEulerTailWeight r) := by
  have hinj : Function.Injective (fun pk : Nat.Primes × ℕ => (pk.1, pk.2 + (r - 2))) := by
    intro a b h
    have hp := congrArg (fun pk : Nat.Primes × ℕ => pk.1) h
    have hk := congrArg (fun pk : Nat.Primes × ℕ => pk.2) h
    exact Prod.ext hp (Nat.add_right_cancel hk)
  have hs := (summable_xiMassPrimePowerCriticalWeight_high.mul_left 2).comp_injective hinj
  refine hs.congr fun pk => ?_
  change 2 * xiMassPrimePowerCriticalWeight pk.1 (pk.2 + (r - 2) + 2) =
    2 * xiMassPrimePowerCriticalWeight pk.1 (pk.2 + r)
  rw [show pk.2 + (r - 2) + 2 = pk.2 + r by omega]

private theorem two_le_of_summable_criticalEuler_slice (r : ℕ)
    (hs : Summable (fun p : Nat.Primes => 2 * xiMassPrimePowerCriticalWeight p r)) :
    2 ≤ r := by
  have hc : 0 < 2 * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(((r : ℝ) + 1) / 2))) := by
    apply Summable.of_nonneg_of_le (fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun p => ?_) (hs.mul_left ((2 * Real.log 2)⁻¹))
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast p.property.two_le)
    have hcoeff : 1 ≤ (2 * Real.log 2)⁻¹ * (2 * Real.log (p : ℝ)) := by
      calc
        1 = (2 * Real.log 2)⁻¹ * (2 * Real.log 2) := (inv_mul_cancel₀ hc.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by norm_num))
          (inv_nonneg.mpr hc.le)
    calc
      _ = 1 * (p : ℝ) ^ (-(((r : ℝ) + 1) / 2)) := (one_mul _).symm
      _ ≤ ((2 * Real.log 2)⁻¹ * (2 * Real.log (p : ℝ))) *
          (p : ℝ) ^ (-(((r : ℝ) + 1) / 2)) :=
        mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [xiMassPrimePowerCriticalWeight_eq]; ring
  have ht := (GaloisForLFunctions.RHTower.summable_prime_rpow_neg_iff
    (((r : ℝ) + 1) / 2)).mp hp
  by_contra hr
  have hn : r ≤ 1 := by omega
  have hnR : (r : ℝ) ≤ 1 := by exact_mod_cast hn
  linarith only [ht, hnR]

/-- Absolute coefficient payment over all primes starts exactly at cubes. -/
theorem summable_criticalEulerTailWeight_iff (r : ℕ) :
    Summable (criticalEulerTailWeight r) ↔ 2 ≤ r := by
  constructor
  · intro hs
    have hinj : Function.Injective (fun p : Nat.Primes => (p, (0 : ℕ))) := by
      intro p q h
      exact congrArg Prod.fst h
    have hslice := hs.comp_injective hinj
    change Summable (fun p : Nat.Primes => 2 * xiMassPrimePowerCriticalWeight p (0 + r)) at hslice
    apply two_le_of_summable_criticalEuler_slice r
    simpa only [zero_add] using hslice
  · exact summable_criticalEulerTailWeight_of_two_le

/-- The first-prime coefficients alone already prevent absolute coefficient summation. -/
theorem not_summable_criticalPrimeCoefficients :
    ¬ Summable (fun p : Nat.Primes => criticalEulerTailWeight 0 (p, 0)) := by
  intro hs
  have h := two_le_of_summable_criticalEuler_slice 0
    (by simpa only [criticalEulerTailWeight, zero_add] using hs)
  omega

/-- The actual square-prime coefficient is twice the logarithmic prime harmonic weight. -/
theorem criticalEulerTailWeight_square (p : Nat.Primes) :
    criticalEulerTailWeight 1 (p, 0) = 2 * Real.log (p : ℝ) / (p : ℝ) := by
  simp only [criticalEulerTailWeight, zero_add, xiMassPrimePowerCriticalWeight_eq, Nat.cast_one]
  rw [show -(((1 : ℝ) + 1) / 2) = -(1 : ℝ) by norm_num,
    Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_one]
  ring

/-- Removing the first-prime layer still leaves divergent absolute square-prime mass. -/
theorem not_summable_criticalSquareCoefficients :
    ¬ Summable (fun p : Nat.Primes => 2 * Real.log (p : ℝ) / (p : ℝ)) := by
  intro hs
  have hslice : Summable (fun p : Nat.Primes => 2 * xiMassPrimePowerCriticalWeight p 1) := by
    refine hs.congr fun p => ?_
    exact (criticalEulerTailWeight_square p).symm
  have h := two_le_of_summable_criticalEuler_slice 1 hslice
  omega

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.criticalEulerTailWeight_eq
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.summable_criticalEulerTailWeight_iff
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.not_summable_criticalPrimeCoefficients
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.not_summable_criticalSquareCoefficients
