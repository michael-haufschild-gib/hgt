/-
The two positive-prime-power support interfaces are one interface.

`PrimeProfileSupportedOnPositivePrimePowers` (profile-packet layer) and
`SupportedOnPositivePrimePowers` (valuation-echelon layer) are the same predicate: an arithmetic
function whose nonzero values sit on positive prime powers.  They were stated separately so the
profile leaf need not import the echelon development, but the two theorem sets then never meet.

This bridge module imports both and identifies them, so the profile layer's realizations discharge
the echelon layer's support premise:

* `supportedOnPositivePrimePowers_zero` — the zero profile;
* `supportedOnPositivePrimePowers_indicator` — the indicator of any positive prime power.

Both are witnesses the echelon side had no source for.
-/
import GaloisForLFunctions.HTGeometry.PrimeProfileClockWitnesses
import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

/-- The profile-layer and echelon-layer support interfaces coincide. -/
theorem primeProfileSupportedOnPositivePrimePowers_iff_supportedOnPositivePrimePowers
    (f : ArithmeticFunction ℂ) :
    PrimeProfileSupportedOnPositivePrimePowers f ↔ SupportedOnPositivePrimePowers f := Iff.rfl

/-- The echelon-layer premise, read from a profile-layer datum. -/
theorem SupportedOnPositivePrimePowers.ofPrimeProfile {f : ArithmeticFunction ℂ}
    (hf : PrimeProfileSupportedOnPositivePrimePowers f) : SupportedOnPositivePrimePowers f := hf

/-- The profile-layer premise, read from an echelon-layer datum. -/
theorem PrimeProfileSupportedOnPositivePrimePowers.ofEchelon {f : ArithmeticFunction ℂ}
    (hf : SupportedOnPositivePrimePowers f) : PrimeProfileSupportedOnPositivePrimePowers f := hf

/-- **The zero arithmetic function is supported on positive prime powers.** -/
theorem supportedOnPositivePrimePowers_zero : SupportedOnPositivePrimePowers 0 :=
  primeProfileSupportedOnPositivePrimePowers_zero

/-- **The indicator of a positive prime power is supported on positive prime powers.** -/
theorem supportedOnPositivePrimePowers_indicator (p : Nat.Primes) (e : ℕ) :
    SupportedOnPositivePrimePowers
      ⟨fun n => if n = (p : ℕ) ^ (e + 1) then 1 else 0, by
        have hp : (p : ℕ) ^ (e + 1) ≠ 0 := pow_ne_zero _ p.2.ne_zero
        simp [Ne.symm hp]⟩ :=
  primeProfileSupportedOnPositivePrimePowers_indicator p e

end GaloisForLFunctions.HTGeometry
