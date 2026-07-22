/-
# Prime-valuation collision classification for Suzuki seam transport

Suzuki's visible prime-power translations move a boundary germ by integer combinations of
`log p`.  Iterated words can collide spatially, so a graded transport proof must know whether two
apparently different valuation labels describe the same point.  The existing weld layer already
proves that the full prime-log family is `ℤ`-linearly independent.  This file turns that result into
the exact seam-coordinate interface needed by the completed zero-mode route:

* `primeSeamCoordinate_injective` says same-end seam collisions are exactly equality of complete
  prime-valuation vectors;
* `rightPrimeSeamLocation_eq_iff` and `leftPrimeSeamLocation_eq_iff` expose that classification at
  the two endpoints of an aperture;
* `right_eq_leftPrimeSeamLocation_iff` isolates every opposite-end collision as one exact affine
  resonance equation.

These are unconditional arithmetic and affine statements.  They do not assert existence or
convergence of Suzuki's analytic log-conormal expansion.
-/
import GaloisForLFunctions.RHTower.WeldRateLattice

open Real

namespace GaloisForLFunctions
namespace RHTower

/-- Complete signed prime-valuation vector mapped to its logarithmic displacement. -/
noncomputable def primeSeamCoordinate : (Nat.Primes →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p : ℕ))

/-- Expansion of the seam coordinate as the finite valuation-weighted prime-log sum. -/
theorem primeSeamCoordinate_apply (ν : Nat.Primes →₀ ℤ) :
    primeSeamCoordinate ν = ν.sum (fun p z => z • Real.log (p : ℕ)) := by
  rw [primeSeamCoordinate, Finsupp.linearCombination_apply]

/-- **Same-end collision classification.**  Unique factorization, through independence of all
prime logarithms, makes the valuation-to-position map injective. -/
theorem primeSeamCoordinate_injective : Function.Injective primeSeamCoordinate := by
  intro ν μ h
  apply sub_eq_zero.mp
  apply (linearIndependent_iff.mp primeLog_linearIndependent)
  change (Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p : ℕ))) ν =
    (Finsupp.linearCombination ℤ (fun p : Nat.Primes => Real.log (p : ℕ))) μ at h
  rw [map_sub, h, sub_self]

/-- Equality of logarithmic seam displacements is exactly equality of valuation labels. -/
theorem primeSeamCoordinate_eq_iff (ν μ : Nat.Primes →₀ ℤ) :
    primeSeamCoordinate ν = primeSeamCoordinate μ ↔ ν = μ :=
  primeSeamCoordinate_injective.eq_iff

/-- Seam emitted from the right endpoint after net prime-valuation displacement `ν`. -/
noncomputable def rightPrimeSeamLocation (a : ℝ) (ν : Nat.Primes →₀ ℤ) : ℝ :=
  a - primeSeamCoordinate ν

/-- Seam emitted from the left endpoint after net prime-valuation displacement `ν`. -/
noncomputable def leftPrimeSeamLocation (a : ℝ) (ν : Nat.Primes →₀ ℤ) : ℝ :=
  -a + primeSeamCoordinate ν

/-- Right-end descendants collide exactly when their full prime-valuation vectors agree. -/
theorem rightPrimeSeamLocation_eq_iff (a : ℝ) (ν μ : Nat.Primes →₀ ℤ) :
    rightPrimeSeamLocation a ν = rightPrimeSeamLocation a μ ↔ ν = μ := by
  constructor
  · intro h
    apply primeSeamCoordinate_injective
    unfold rightPrimeSeamLocation at h
    linarith
  · rintro rfl
    rfl

/-- Left-end descendants collide exactly when their full prime-valuation vectors agree. -/
theorem leftPrimeSeamLocation_eq_iff (a : ℝ) (ν μ : Nat.Primes →₀ ℤ) :
    leftPrimeSeamLocation a ν = leftPrimeSeamLocation a μ ↔ ν = μ := by
  constructor
  · intro h
    apply primeSeamCoordinate_injective
    unfold leftPrimeSeamLocation at h
    linarith
  · rintro rfl
    rfl

/-- **Opposite-end resonance law.**  A right descendant and a left descendant meet precisely when
twice the aperture equals the sum of their logarithmic valuation displacements. -/
theorem right_eq_leftPrimeSeamLocation_iff (a : ℝ) (ν μ : Nat.Primes →₀ ℤ) :
    rightPrimeSeamLocation a ν = leftPrimeSeamLocation a μ ↔
      2 * a = primeSeamCoordinate ν + primeSeamCoordinate μ := by
  unfold rightPrimeSeamLocation leftPrimeSeamLocation
  constructor <;> intro h <;> linarith

end RHTower
end GaloisForLFunctions
