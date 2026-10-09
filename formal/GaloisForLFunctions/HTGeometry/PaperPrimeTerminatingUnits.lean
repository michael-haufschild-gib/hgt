import GaloisForLFunctions.HTGeometry.PaperTerminatingCoreUnits
import GaloisForLFunctions.HTGeometry.PaperPrimeTerminatingSlice
import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeFlow

/-!
# Exact arithmetic unit and denominator tests for prime cores

The entire prime core, rather than a finite-prime chart, has an explicit
unit test: nonzero coefficient at one and no support on prime multiples.
The same support condition characterizes all localizations preserving its
locally nilpotent clock, including the zero denominator.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

/-- In the full core, invertibility is exactly a nonzero identity coefficient and p-free support. -/
theorem paperPrimeTerminatingCore_isUnit_iff (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    IsUnit f ↔ (f : ArithmeticFunction ℂ) 1 ≠ 0 ∧
      ∀ n : ℕ, (p : ℕ) ∣ n → (f : ArithmeticFunction ℂ) n = 0 := by
  have h := paperTerminatingCore_isUnit_iff (primeArithmeticDerivation (p : ℕ) p.property) f
  simpa only [ArithmeticFunction.isUnit_iff_isUnit_apply_one, isUnit_iff_ne_zero,
    paperPrimeArithmetic_kernel_iff] using h

/-- The full coefficient algebra in the polynomial presentation reflects ambient units. -/
theorem paperPrimeConstants_isUnit_iff (p : Nat.Primes) (a : paperPrimeConstants p) :
    IsUnit a ↔ (a : ArithmeticFunction ℂ) 1 ≠ 0 := by
  rw [← Polynomial.isUnit_C,
    ← isUnit_map_iff (paperPrimeTerminatingSlice p) (Polynomial.C a),
    paperPrimeTerminatingCore_isUnit_iff]
  simp only [paperPrimeTerminatingSlice_C]
  exact and_iff_left ((paperPrimeConstants_mem_iff p _).mp a.property)

/-- A native localization keeps the complete core clock exactly at p-free denominators. -/
theorem paperPrimeTerminatingCore_localization_support_iff (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    IsLocallyNilpotent
      (paperNativeLocalization (S := Localization.Away f) (Submonoid.powers f)
        (paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property))) ↔
      ∀ n : ℕ, (p : ℕ) ∣ n → (f : ArithmeticFunction ℂ) n = 0 := by
  have h := paperTerminatingCore_localization_iff
    (primeArithmeticDerivation (p : ℕ) p.property) f
  exact h.trans (paperPrimeArithmetic_kernel_iff p _)

/-- Inverting the literal Möbius source destroys local nilpotence of every prime core clock. -/
theorem paperMoebius_prime_core_localization_not_locallyNilpotent (p : Nat.Primes) :
    ¬ IsLocallyNilpotent
      (paperNativeLocalization (S := Localization.Away (paperMoebiusInPrimeCore p))
        (Submonoid.powers (paperMoebiusInPrimeCore p))
        (paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property))) := by
  intro h
  exact paperMoebius_prime_derivative_ne_zero p
    ((paperTerminatingCore_localization_iff
      (primeArithmeticDerivation (p : ℕ) p.property) (paperMoebiusInPrimeCore p)).mp h)

/-- Every scalar-shifted prime coordinate is an obstructing denominator in the full core. -/
theorem paperPrimeTerminating_shifted_generator_localization_not_locallyNilpotent
    (p : Nat.Primes) (c : ℂ) :
    ¬ IsLocallyNilpotent
      (paperNativeLocalization
        (S := Localization.Away (paperPrimeTerminatingGenerator p +
          algebraMap ℂ (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) c))
        (Submonoid.powers (paperPrimeTerminatingGenerator p +
          algebraMap ℂ (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) c))
        (paperTerminatingClock (primeArithmeticDerivation (p : ℕ) p.property))) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  let f := paperPrimeTerminatingGenerator p + algebraMap ℂ (paperTerminatingCore D) c
  have hclock : paperTerminatingClock D f = 1 := by simp [f, D]
  intro h
  have hz : paperTerminatingClock D f = 0 :=
    Subtype.ext ((paperTerminatingCore_localization_iff D f).mp h)
  exact one_ne_zero (hclock.symm.trans hz)

end

end GaloisForLFunctions.HTGeometry
