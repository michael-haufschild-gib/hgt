import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource

/-!
# The twin-prime constant in the covariance singular series

At gap two, every odd-prime Ramanujan factor is `1 - (p - 1)⁻²`.
The factor at two is exactly two. Removing it identifies the positive
twin-prime Euler product with half the existing Hardy–Littlewood singular series.
-/

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The odd-prime correction factor, extended by one at the prime two. -/
def twinPrimeFactor (p : Nat.Primes) : ℝ :=
  if (p : ℕ) = 2 then 1 else 1 - 1 / ((p : ℝ) - 1) ^ 2

/-- The classical twin-prime constant as an actual infinite Euler product. -/
def twinPrimeConstant : ℝ := ∏' p : Nat.Primes, twinPrimeFactor p

/-- The odd-prime factors converge to half the gap-two singular series. -/
theorem hasProd_twinPrimeFactor :
    HasProd twinPrimeFactor (hardyLittlewoodSingularSeries 2 / 2) := by
  let twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩
  have h := (hasProd_hardyLittlewoodSingularSeries (h := 2) (by norm_num)).mul
    (hasProd_ite_eq twoPrime (1 / 2 : ℝ))
  have hnormalized : HasProd twinPrimeFactor (hardyLittlewoodSingularSeries 2 * (1 / 2)) := by
    apply h.congr_fun
    intro p
    by_cases hp2 : p = twoPrime
    · subst p
      norm_num [twoPrime, twinPrimeFactor, ramanujanLagWeight_prime]
    · have hpval : (p : ℕ) ≠ 2 := fun he => hp2 (Subtype.ext he)
      have hdiv : ¬ (p : ℕ) ∣ 2 := by
        intro hd
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact p.prop.ne_one h1
        · exact hpval h2
      rw [if_neg hp2, mul_one, twinPrimeFactor, if_neg hpval,
        ramanujanLagWeight_prime p.prop, if_neg hdiv]
      ring
  simpa only [div_eq_mul_inv, one_mul] using hnormalized

/-- The prime-pair covariance normalization differs from the twin-prime constant by two. -/
theorem twinPrimeConstant_eq_singularSeries :
    twinPrimeConstant = hardyLittlewoodSingularSeries 2 / 2 :=
  hasProd_twinPrimeFactor.tprod_eq

/-- The infinite product is strictly positive, not merely nonnegative. -/
theorem twinPrimeConstant_pos : 0 < twinPrimeConstant := by
  rw [twinPrimeConstant_eq_singularSeries]
  exact div_pos (hardyLittlewoodSingularSeries_pos_of_even (by norm_num) (by norm_num))
    (by norm_num)

#print axioms hasProd_twinPrimeFactor
#print axioms twinPrimeConstant_eq_singularSeries
#print axioms twinPrimeConstant_pos
end GaloisForLFunctions.BezoutValuationIncidence
