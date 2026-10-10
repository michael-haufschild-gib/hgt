import GaloisForLFunctions.HTGeometry.PaperMoebiusEulerFactor
import GaloisForLFunctions.HTGeometry.PaperLocallyNilpotentMultipliers

/-!
# A terminating clock with the literal Möbius source as its slice

The p-free zeta coefficient supplies an invariant invertible speed. The
proven invariant-multiplier theorem therefore makes Möbius a slice on the
entire native prime core, including functions outside finite-prime charts.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

private def invariantClockMultiple {B : Type*} [CommRing B] [Algebra ℂ B]
    (q : B) (D : Derivation ℂ B B) : Derivation ℂ B B := q • D

private theorem invariantClockMultiple_locallyNilpotent
    {B : Type*} [CommRing B] [Algebra ℂ B] (q : B) (D : Derivation ℂ B B)
    (hD : IsLocallyNilpotent D) (hq : D q = 0) :
    IsLocallyNilpotent (invariantClockMultiple q D) :=
  paperLND_invariant_smul D hD q hq

/-- The explicit p-free speed normalizing the Möbius derivative to one. -/
def paperMoebiusPrimeSpeed (p : Nat.Primes) : paperPrimeConstants p :=
  -paperPrimeConstantProjection p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

/-- The normalization is an exact convolution inverse, not an assumed unit. -/
theorem paperMoebiusPrimeSpeed_mul_derivative (p : Nat.Primes) :
    (paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ) *
      primeArithmeticDerivation (p : ℕ) p.property
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) = 1 := by
  rw [paperMoebius_prime_derivative_eq_projection]
  change -(paperPrimeConstantProjection p
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
    -(paperPrimeConstantProjection p
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) = 1
  calc
    _ = (paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) *
      (paperPrimeConstantProjection p
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by ring
    _ = 1 := paperMoebius_zeta_prime_constants_inverse p

/-- The normalized clock acts on the original full prime-terminating algebra. -/
def paperMoebiusPrimeClock (p : Nat.Primes) :
    Derivation ℂ
      (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
      (paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  let B := paperTerminatingCore D
  let q : B := ⟨(paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ),
    paperPrimeConstants_le_terminatingCore p (paperMoebiusPrimeSpeed p).property⟩
  let δ : Derivation ℂ B B := paperTerminatingClock D
  exact invariantClockMultiple q δ

@[simp] theorem paperMoebiusPrimeClock_coe (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    (paperMoebiusPrimeClock p f : ArithmeticFunction ℂ) =
      (paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ) *
        primeArithmeticDerivation (p : ℕ) p.property (f : ArithmeticFunction ℂ) := rfl

/-- The source invariant-multiplier theorem pays local nilpotence of the new clock. -/
theorem paperMoebiusPrimeClock_locallyNilpotent (p : Nat.Primes) :
    IsLocallyNilpotent (k := ℂ)
      (A := paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property))
      (paperMoebiusPrimeClock p) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  let q : paperTerminatingCore D := ⟨(paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ),
    paperPrimeConstants_le_terminatingCore p (paperMoebiusPrimeSpeed p).property⟩
  have hq : paperTerminatingClock D q = 0 :=
    Subtype.ext (paperMoebiusPrimeSpeed p).property
  have h := invariantClockMultiple_locallyNilpotent q
    (paperTerminatingClock D) (paperTerminatingClock_locallyNilpotent D) hq
  exact h

/-- Möbius itself is a slice, with no extra arithmetic hypothesis. -/
@[simp] theorem paperMoebiusPrimeClock_moebius (p : Nat.Primes) :
    paperMoebiusPrimeClock p (paperMoebiusInPrimeCore p) = 1 :=
  Subtype.ext (paperMoebiusPrimeSpeed_mul_derivative p)

/-- Normalization preserves exactly the p-free constant algebra. -/
theorem paperMoebiusPrimeClock_kernel_iff (p : Nat.Primes)
    (f : paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property)) :
    paperMoebiusPrimeClock p f = 0 ↔
      ∀ n : ℕ, (p : ℕ) ∣ n → (f : ArithmeticFunction ℂ) n = 0 := by
  have hne : (paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ) ≠ 0 := by
    intro h
    have hunit := paperMoebiusPrimeSpeed_mul_derivative p
    rw [h, zero_mul] at hunit
    exact zero_ne_one hunit
  constructor
  · intro h
    apply (paperPrimeArithmetic_kernel_iff p _).mp
    have he := congrArg Subtype.val h
    change (paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ) *
      primeArithmeticDerivation (p : ℕ) p.property (f : ArithmeticFunction ℂ) = 0 at he
    exact (mul_eq_zero.mp he).resolve_left hne
  · intro h
    apply Subtype.ext
    change (paperMoebiusPrimeSpeed p : ArithmeticFunction ℂ) *
      primeArithmeticDerivation (p : ℕ) p.property (f : ArithmeticFunction ℂ) = 0
    rw [(paperPrimeArithmetic_kernel_iff p _).mpr h, mul_zero]

/-- The normalized formal flow translates the literal source by its time variable. -/
theorem paperMoebiusPrimeClock_formal_orbit (p : Nat.Primes) :
    paperFormalExponential (paperMoebiusPrimeClock p) (paperMoebiusInPrimeCore p) =
      PowerSeries.C (paperMoebiusInPrimeCore p) + PowerSeries.X := by
  have htwo : paperMoebiusPrimeClock p
      (paperMoebiusPrimeClock p (paperMoebiusInPrimeCore p)) = 0 := by simp
  simpa using paperFormalExponential_linear_on (paperMoebiusPrimeClock p)
    (paperMoebiusInPrimeCore p) htwo

end

end GaloisForLFunctions.HTGeometry
