import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeValuationSeam

/-!
# The prime seam coordinate takes positive values in every window

The first-grade observability laws are conditioned on a valuation whose seam coordinate is positive
and below a given width.  The seam coordinate of a single prime is its logarithm, so the positivity
half is free, and the window half holds for every width above half that logarithm — in particular
for every width above `(log 2)/2`, using the valuation concentrated at the smallest prime.
-/

open Real

namespace GaloisForLFunctions
namespace RHTower

/-- **The seam coordinate of a single prime valuation is its weighted logarithm.** -/
theorem primeSeamCoordinate_single (p : Nat.Primes) (z : ℤ) :
    primeSeamCoordinate (Finsupp.single p z) = (z : ℝ) * Real.log (p : ℕ) := by
  rw [primeSeamCoordinate, Finsupp.linearCombination_single, zsmul_eq_mul]

/-- The logarithm of a prime is positive. -/
theorem log_prime_pos (p : Nat.Primes) : 0 < Real.log (p : ℕ) := by
  refine Real.log_pos ?_
  exact_mod_cast p.property.one_lt

/-- **The unit valuation at a prime has positive seam coordinate.** -/
theorem primeSeamCoordinate_single_one_pos (p : Nat.Primes) :
    0 < primeSeamCoordinate (Finsupp.single p 1) := by
  rw [primeSeamCoordinate_single]
  simpa using log_prime_pos p

/-- **Every window wider than half a prime logarithm contains that prime's seam coordinate.** -/
theorem primeSeamCoordinate_single_one_mem_window {p : Nat.Primes} {a : ℝ}
    (ha : Real.log (p : ℕ) < 2 * a) :
    0 < primeSeamCoordinate (Finsupp.single p 1) ∧
      primeSeamCoordinate (Finsupp.single p 1) < 2 * a := by
  refine ⟨primeSeamCoordinate_single_one_pos p, ?_⟩
  rw [primeSeamCoordinate_single]
  simpa using ha

/-- Hence the observability window is inhabited for every positive width beyond half a prime
logarithm. -/
theorem exists_primeSeamCoordinate_mem_window {p : Nat.Primes} {a : ℝ}
    (ha : Real.log (p : ℕ) < 2 * a) :
    ∃ δ : Nat.Primes →₀ ℤ, 0 < primeSeamCoordinate δ ∧ primeSeamCoordinate δ < 2 * a :=
  ⟨Finsupp.single p 1, primeSeamCoordinate_single_one_mem_window ha⟩

end RHTower
end GaloisForLFunctions
