import GaloisForLFunctions.HTGeometry.PadicPowerSeriesEvaluation
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Dyadic Euler factors in the Birch--Tate specialization

At a prime above `2`, the residue-field cardinality is `2^f` with `f > 0`. Hence the removed
weight-two Euler factor has absolute value `2^f - 1`, which is a `2`-adic unit. This module records
the elementary valuation and unit statements used by the dyadic specialization.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A positive power of `2`, minus one, is odd. -/
theorem two_not_dvd_two_pow_succ_sub_one (f : ℕ) :
    ¬2 ∣ 2 ^ (f + 1) - 1 := by
  simpa [pow_succ, Nat.mul_comm] using
    Nat.two_not_dvd_two_mul_sub_one (pow_pos (by decide : 0 < 2) f)

/-- Removed Euler factors at primes above `2` have zero `2`-adic valuation. -/
theorem two_padicValNat_pow_succ_sub_one_eq_zero (f : ℕ) :
    padicValNat 2 (2 ^ (f + 1) - 1) = 0 :=
  padicValNat.eq_zero_of_not_dvd (two_not_dvd_two_pow_succ_sub_one f)

/-- Removed Euler factors at primes above `2` are units in `ℤ₂`. -/
theorem two_power_succ_sub_one_isUnit (f : ℕ) :
    IsUnit (((2 ^ (f + 1) - 1 : ℕ) : ℤ_[2])) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff,
    Nat.prime_two.coprime_iff_not_dvd]
  exact two_not_dvd_two_pow_succ_sub_one f

end GaloisForLFunctions.HTGeometry
