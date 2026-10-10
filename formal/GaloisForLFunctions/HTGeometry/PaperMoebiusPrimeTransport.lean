import GaloisForLFunctions.HTGeometry.PaperMoebiusEulerFactor
import GaloisForLFunctions.HTGeometry.PaperLNDLinearAction
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoactionAction

/-!
# Scalar specialization of the literal Möbius prime flow

This is the source additive action evaluated on the original Möbius element
of the full prime core. Its exact coefficient formula exposes the sharp
ambient-unit boundary: invertibility fails precisely at time one.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate CoactionLND

noncomputable section

attribute [local instance 2000] Algebra.toModule
attribute [local instance 2100] Semiring.toModule

/-- Evaluate the proven full-core action on the literal Möbius source. -/
def paperMoebiusPrimeTransport (p : Nat.Primes) (t : ℂ) : ArithmeticFunction ℂ :=
  ((paperTerminatingAction (primeArithmeticDerivation (p : ℕ) p.property)).specialize t
    (paperMoebiusInPrimeCore p) : ArithmeticFunction ℂ)

/-- The specialized action has a literal p-free coefficient formula at every complex time. -/
theorem paperMoebiusPrimeTransport_eq (p : Nat.Primes) (t : ℂ) :
    paperMoebiusPrimeTransport p t = (ArithmeticFunction.moebius : ArithmeticFunction ℂ) -
      t • (paperPrimeConstantProjection p
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) := by
  let D := primeArithmeticDerivation (p : ℕ) p.property
  have htwo : paperTerminatingClock D
      (paperTerminatingClock D (paperMoebiusInPrimeCore p)) = 0 :=
    Subtype.ext (paperMoebius_prime_iterate_two p)
  have horbit := paperLND_exponential_linear_on (paperTerminatingClock D)
    (paperTerminatingClock_locallyNilpotent D) (paperMoebiusInPrimeCore p) htwo
  change (paperTerminatingAction D).toAlgHom (paperMoebiusInPrimeCore p) = _ at horbit
  change ((((paperTerminatingAction D).toAlgHom (paperMoebiusInPrimeCore p)).eval
    (algebraMap ℂ (paperTerminatingCore D) t) : paperTerminatingCore D) :
      ArithmeticFunction ℂ) = _
  rw [horbit]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  change (ArithmeticFunction.moebius : ArithmeticFunction ℂ) +
    primeArithmeticDerivation (p : ℕ) p.property
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
        algebraMap ℂ (ArithmeticFunction ℂ) t = _
  rw [paperMoebius_prime_derivative_eq_projection, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm]
  simp [sub_eq_add_neg]

/-- Coefficients divisible by p are fixed; every other coefficient is multiplied by 1-t. -/
theorem paperMoebiusPrimeTransport_apply (p : Nat.Primes) (t : ℂ) (n : ℕ) :
    paperMoebiusPrimeTransport p t n =
      (if (p : ℕ) ∣ n then 1 else 1 - t) * (ArithmeticFunction.moebius n : ℂ) := by
  rw [paperMoebiusPrimeTransport_eq]
  change (ArithmeticFunction.moebius : ArithmeticFunction ℂ) n -
    t * (paperPrimeConstantProjection p
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ArithmeticFunction ℂ) n = _
  rw [paperPrimeConstantProjection_apply]
  by_cases hn : (p : ℕ) ∣ n
  · simp [hn, ArithmeticFunction.intCoe_apply]
  · simp only [if_neg hn, ArithmeticFunction.intCoe_apply]
    ring

@[simp] theorem paperMoebiusPrimeTransport_one (p : Nat.Primes) (t : ℂ) :
    paperMoebiusPrimeTransport p t 1 = 1 - t := by
  simp [paperMoebiusPrimeTransport_apply, p.property.not_dvd_one]

/-- The exact ambient unit boundary is the single scalar time one. -/
theorem paperMoebiusPrimeTransport_isUnit_iff (p : Nat.Primes) (t : ℂ) :
    IsUnit (paperMoebiusPrimeTransport p t) ↔ t ≠ 1 := by
  rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, isUnit_iff_ne_zero,
    paperMoebiusPrimeTransport_one]
  constructor
  · intro ht he
    apply ht
    rw [he, sub_self]
  · intro ht he
    exact ht (sub_eq_zero.mp he).symm

/-- Time one cannot extend to any unital algebra map on all arithmetic functions. -/
theorem paperMoebiusPrimeTransport_one_no_ambient_extension (p : Nat.Primes) :
    ¬ ∃ F : ArithmeticFunction ℂ →ₐ[ℂ] ArithmeticFunction ℂ,
      F (ArithmeticFunction.moebius : ArithmeticFunction ℂ) =
        paperMoebiusPrimeTransport p 1 := by
  rintro ⟨F, hF⟩
  have hu := paperMoebius_ambient_isUnit.map F
  rw [hF, paperMoebiusPrimeTransport_isUnit_iff] at hu
  exact hu rfl

end

end GaloisForLFunctions.HTGeometry
