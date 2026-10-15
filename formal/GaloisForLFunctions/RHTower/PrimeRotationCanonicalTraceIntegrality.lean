import GaloisForLFunctions.HTGeometry.PaperRotationPolynomialTraceIntegrality
import GaloisForLFunctions.RHTower.PaperPrimeRotationIdealTrace

/-!
# Native prime rotation: canonical trace integrality

The native prime frequency has infinite order at every positive clock
step. Consequently its actual finite Weyl algebra embeds faithfully into
the quantum Laurent division ring, with matching canonical trace. Every
matrix idempotent has natural-number trace; differences of idempotents have
integer trace. All clocks use `q+1`, so irrationality is proved internally.

This is a theorem about concrete finite operator algebras. It supplies no
unproved Xi projective representative or Chern/multiplicity identification.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

private theorem prime_clock_infinite (p : Nat.Primes) (q : ℕ) (b : ℤ) :
    paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1)) = 1 ↔ b = 0 := by
  simpa only [Nat.add_eq_zero_iff, one_ne_zero, and_false, false_or] using
    paperPrimeRotationPhase_int_eq_one p (q + 1) b

/-- Native prime clocks give the literal constant-coefficient canonical trace. -/
theorem paperPrimeRotationCanonicalTrace_word (p : Nat.Primes) (q : ℕ) (a b : ℤ) :
    paperRotationTrace (paperRotationWord a ((b : ℝ) * paperPrimeRotationFrequency p (q + 1))) =
      if a = 0 ∧ b = 0 then 1 else 0 :=
  paperRotationTrace_integer_word _ (prime_clock_infinite p q) a b

/-- The native finite prime-rotation algebra has an explicit faithful realization in the
quantum Laurent division ring. -/
def paperPrimeRotationPolynomialLift (p : Nat.Primes) (q : ℕ) :
    paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)) →ₐ[ℂ]
      QuantumLaurentDivisionRing (paperRotationQuantumUnit (paperPrimeRotationFrequency p (q + 1))) :=
  paperRotationPolynomialLift _ (prime_clock_infinite p q)

theorem paperPrimeRotationPolynomialLift_injective (p : Nat.Primes) (q : ℕ) :
    Function.Injective (paperPrimeRotationPolynomialLift p q) :=
  paperRotationPolynomialLift_injective _ (prime_clock_infinite p q)

/-- Integer canonical trace for every actual matrix idempotent over the native finite
prime-Weyl algebra. No trace, projective-lift, or irrationality premise is supplied. -/
theorem paperPrimeRotationPolynomial_idempotent_trace_eq_nat (p : Nat.Primes) (q : ℕ)
    {n : ℕ} (E : Matrix (Fin n) (Fin n)
      (paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))))
    (hE : E * E = E) :
    ∃ r : ℕ, (∑ i, paperRotationTrace (E i i).val) = (r : ℂ) :=
  paperRotationPolynomial_idempotent_trace_eq_nat _ (prime_clock_infinite p q) E hE

/-- Differences of actual finite projective representatives also have integer canonical trace. -/
theorem paperPrimeRotationPolynomial_virtual_trace_eq_int (p : Nat.Primes) (q : ℕ)
    {n m : ℕ}
    (E : Matrix (Fin n) (Fin n)
      (paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))))
    (F : Matrix (Fin m) (Fin m)
      (paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))))
    (hE : E * E = E) (hF : F * F = F) :
    ∃ k : ℤ, (∑ i, paperRotationTrace (E i i).val) -
      (∑ j, paperRotationTrace (F j j).val) = (k : ℂ) := by
  obtain ⟨r, hr⟩ := paperPrimeRotationPolynomial_idempotent_trace_eq_nat p q E hE
  obtain ⟨s, hs⟩ := paperPrimeRotationPolynomial_idempotent_trace_eq_nat p q F hF
  refine ⟨(r : ℤ) - s, ?_⟩
  rw [hr, hs]
  push_cast
  rfl

end
end RHTower
