import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusPolynomialPrimitives
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteField.FrobeniusFixedCardinality


/-!
# Exact counts of polynomial Frobenius primitives

At a divisible period, translation by the trace polynomial identifies
all polynomial primitives with the fixed subfield of the short Frobenius.
The gcd formula for finite-field fixed points therefore counts the full
solution set, while nondivisible periods have no solutions.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Polynomial GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p]

/-- The literal polynomial solutions of a two-term Frobenius difference equation. -/
def FrobeniusPolynomialPrimitives (r n : ℕ) :=
  {P : K[X] // P ^ p ^ (r + 1) - P = X ^ p ^ n - X}

/-- Translation by the trace polynomial parametrizes every primitive by a fixed constant. -/
def frobeniusPolynomialPrimitiveEquiv (r m : ℕ) :
    frobeniusFixedSubfield p K (r + 1) ≃
      FrobeniusPolynomialPrimitives p K r ((r + 1) * m) := by
  let f : frobeniusFixedSubfield p K (r + 1) →
      FrobeniusPolynomialPrimitives p K r ((r + 1) * m) := fun a =>
    ⟨frobeniusTraceSum p (r + 1) m X + C (a : K),
      (polynomial_frobenius_primitive_trace_iff p r m _).mpr ⟨a, a.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    have he := congrArg Subtype.val h
    have hC : C (a : K) = C (b : K) := add_left_cancel he
    exact Subtype.ext (Polynomial.C_injective hC)
  · intro P
    obtain ⟨a, ha, he⟩ := (polynomial_frobenius_primitive_trace_iff p r m P.val).mp P.property
    exact ⟨⟨a, ha⟩, Subtype.ext he.symm⟩

variable [Finite K] [Algebra (ZMod p) K]

/-- The number of primitives at a divisible period is the cardinality of the short Frobenius fixed field. -/
theorem frobeniusPolynomialPrimitives_card_mul (r m : ℕ) :
    Nat.card (FrobeniusPolynomialPrimitives p K r ((r + 1) * m)) =
      p ^ Nat.gcd (Module.finrank (ZMod p) K) (r + 1) :=
  (Nat.card_congr (frobeniusPolynomialPrimitiveEquiv p K r m)).symm.trans
    (frobeniusFixedSubfield_card p K (r + 1))

/-- The exact number of polynomial primitives, including the empty nondivisible-period case. -/
theorem frobeniusPolynomialPrimitives_card (r n : ℕ) :
    Nat.card (FrobeniusPolynomialPrimitives p K r n) =
      if r + 1 ∣ n then p ^ Nat.gcd (Module.finrank (ZMod p) K) (r + 1) else 0 := by
  by_cases hd : r + 1 ∣ n
  · rw [if_pos hd]
    have h := frobeniusPolynomialPrimitives_card_mul p K r (n / (r + 1))
    simpa only [Nat.mul_div_cancel' hd] using h
  · rw [if_neg hd]
    letI : IsEmpty (FrobeniusPolynomialPrimitives p K r n) :=
      ⟨fun P => hd ((exists_polynomial_frobenius_difference_iff p r n).mp ⟨P.val, P.property⟩)⟩
    simp

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
