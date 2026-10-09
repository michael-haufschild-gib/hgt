import GaloisForLFunctions.HTGeometry.PaperPrimePolynomialClocks
import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization

/-!
# Which arithmetic denominators preserve a prime clock?

Source factorial closure and invariant localization give the exact boundary.
A shifted active prime coordinate is never a unit in its polynomial chart,
although every nonzero constant shift is a unit in the full convolution
algebra. Inverting a denominator preserves the clock exactly when that
denominator is invariant; all prime clocks survive together only on scalars.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

local instance (S : Finset Nat.Primes) : CharZero (paperPrimePolynomialAlgebra S) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (paperPrimePolynomialAlgebra S)).injective

/-- Every scalar translate of a prime coordinate remains an exact clock coordinate. -/
theorem paperPrimePolynomialClock_shifted_generator (S : Finset Nat.Primes) (p : S) (c : ℂ) :
    paperPrimePolynomialClock S p
      (paperPrimePolynomialGenerator S p + algebraMap ℂ (paperPrimePolynomialAlgebra S) c) = 1 := by
  simp

/-- A shifted active coordinate cannot be a unit inside its polynomial chart. -/
theorem paperPrimePolynomial_shifted_generator_not_isUnit
    (S : Finset Nat.Primes) (p : S) (c : ℂ) :
    ¬ IsUnit (paperPrimePolynomialGenerator S p +
      algebraMap ℂ (paperPrimePolynomialAlgebra S) c) := by
  rintro ⟨u, hu⟩
  have he := paperLocallyNilpotent_kills_unit (k := ℂ) (A := paperPrimePolynomialAlgebra S)
    (paperPrimePolynomialClock S p)
    (paperPrimePolynomialClock_locallyNilpotent S p) u
  rw [hu, paperPrimePolynomialClock_shifted_generator] at he
  exact one_ne_zero he

/-- In the full convolution algebra the very same shift is a unit exactly at nonzero constant term. -/
theorem paperPrimePolynomial_shifted_generator_ambient_isUnit_iff
    (S : Finset Nat.Primes) (p : S) (c : ℂ) :
    IsUnit ((paperPrimePolynomialGenerator S p : ArithmeticFunction ℂ) +
      algebraMap ℂ (ArithmeticFunction ℂ) c) ↔ c ≠ 0 := by
  rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one]
  simp [paperPrimePolynomialGenerator_coe, paperPrimeCoordinate, arithmeticOfPrimeColumn,
    ArithmeticFunction.algebraMap_apply_one, isUnit_iff_ne_zero, Nat.not_prime_one]

/-- An arbitrary arithmetic polynomial denominator preserves a prime clock exactly when fixed. -/
theorem paperPrimePolynomialLocalization_iff (S : Finset Nat.Primes) (p : S)
    (a : paperPrimePolynomialAlgebra S) :
    IsLocallyNilpotent (k := ℂ) (A := Localization.Away a)
      (paperNativeLocalization (k := ℂ) (A := paperPrimePolynomialAlgebra S)
        (S := Localization.Away a) (Submonoid.powers a)
        (paperPrimePolynomialClock S p)) ↔ paperPrimePolynomialClock S p a = 0 := by
  have h := paperNativeAway_locallyNilpotent_iff (k := ℂ) (A := paperPrimePolynomialAlgebra S)
    (paperPrimePolynomialClock S p) (paperPrimePolynomialClock_locallyNilpotent S p) a
  exact h

/-- Inverting any scalar translate of the active prime variable destroys termination. -/
theorem paperPrimePolynomialLocalization_shifted_generator_not_locallyNilpotent
    (S : Finset Nat.Primes) (p : S) (c : ℂ) :
    ¬ IsLocallyNilpotent (k := ℂ)
      (A := Localization.Away (paperPrimePolynomialGenerator S p +
        algebraMap ℂ (paperPrimePolynomialAlgebra S) c))
      (paperNativeLocalization (k := ℂ) (A := paperPrimePolynomialAlgebra S)
        (S := Localization.Away (paperPrimePolynomialGenerator S p +
          algebraMap ℂ (paperPrimePolynomialAlgebra S) c))
        (Submonoid.powers (paperPrimePolynomialGenerator S p +
          algebraMap ℂ (paperPrimePolynomialAlgebra S) c)) (paperPrimePolynomialClock S p)) := by
  rw [paperPrimePolynomialLocalization_iff, paperPrimePolynomialClock_shifted_generator]
  exact one_ne_zero

/-- Inverting a prime coordinate preserves exactly the clocks of the other primes. -/
theorem paperPrimePolynomialLocalization_generator_iff
    (S : Finset Nat.Primes) (p q : S) :
    IsLocallyNilpotent (k := ℂ) (A := Localization.Away (paperPrimePolynomialGenerator S q))
      (paperNativeLocalization (k := ℂ) (A := paperPrimePolynomialAlgebra S)
        (S := Localization.Away (paperPrimePolynomialGenerator S q))
        (Submonoid.powers (paperPrimePolynomialGenerator S q)) (paperPrimePolynomialClock S p)) ↔
      q ≠ p := by
  classical
  rw [paperPrimePolynomialLocalization_iff, paperPrimePolynomialClock_generator]
  by_cases h : q = p <;> simp [h]

/-- A common denominator preserves every prime clock exactly when it is scalar, including zero. -/
theorem paperPrimePolynomialLocalization_all_iff (S : Finset Nat.Primes)
    (a : paperPrimePolynomialAlgebra S) :
    (∀ p : S, IsLocallyNilpotent (k := ℂ) (A := Localization.Away a)
      (paperNativeLocalization (k := ℂ) (A := paperPrimePolynomialAlgebra S)
        (S := Localization.Away a) (Submonoid.powers a)
        (paperPrimePolynomialClock S p))) ↔
      ∃ c : ℂ, a = algebraMap ℂ (paperPrimePolynomialAlgebra S) c := by
  simp only [paperPrimePolynomialLocalization_iff]
  exact paperPrimePolynomialClock_common_kernel S a

end

end GaloisForLFunctions.HTGeometry
