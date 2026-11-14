import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction
import GaloisForLFunctions.RHTower.PowerSievedLiouvilleDirichlet
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# Prime partitions of power sieves

The perfect-power indicator, the power-sieved Liouville stream and the power-free indicator
all split into complementary prime restrictions. The Möbius normalization of the power sieve
also holds inside each restricted convolution algebra.
-/

noncomputable section

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction RHTower

/-- Perfect-power detection factors over arbitrary complementary prime sets. -/
theorem powerIndicator_prime_partition (S : Set ℕ) (m : ℕ) :
    primeRestrict S (powerIndicator m) * primeRestrict Sᶜ (powerIndicator m) =
      powerIndicator m :=
  primeRestrict_mul_compl S _ (isMultiplicative_powerIndicator m)

/-- The coefficients of `ζ(ms)/ζ(s)` admit the same exact prime separation. -/
theorem sievedLiouville_prime_partition (S : Set ℕ) (m : ℕ) :
    primeRestrict S (sievedLiouville m) * primeRestrict Sᶜ (sievedLiouville m) =
      sievedLiouville m :=
  primeRestrict_mul_compl S _ (isMultiplicative_sievedLiouville m)

/-- Power-free detection splits for every positive power exponent. -/
theorem mFreeIndicator_prime_partition (S : Set ℕ) (m : ℕ) :
    primeRestrict S (mFreeIndicator (m + 1)) *
      primeRestrict Sᶜ (mFreeIndicator (m + 1)) = mFreeIndicator (m + 1) :=
  primeRestrict_mul_compl S _ (isMultiplicative_mFreeIndicator (Nat.succ_ne_zero m))

/-- Möbius normalization survives an arbitrary, possibly infinite, prime restriction. -/
theorem restricted_zeta_mul_sievedLiouville (S : Set ℕ) (m : ℕ) :
    primeRestrict S (zeta : ArithmeticFunction ℂ) * primeRestrict S (sievedLiouville m) =
      primeRestrict S (powerIndicator m) := by
  rw [← primeRestrict_mul, zeta_mul_sievedLiouville]

end GaloisForLFunctions.SelbergClass.DirichletSeries
