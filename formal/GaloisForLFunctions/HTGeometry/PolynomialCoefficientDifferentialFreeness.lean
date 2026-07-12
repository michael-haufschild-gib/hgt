import GaloisForLFunctions.HTGeometry.PolynomialPatternRectangularization

/-!
# Polynomial-coefficient differential freeness on finite translate packets

The countable-pattern source theorem implies the conventional relation statement for every finite
injective translate packet: if a multivariate differential polynomial with coefficients in `C[z]`
vanishes throughout the common upper domain of the translated prime-log source, then the
polynomial itself is zero.

The proof is constraint-side.  It canonicalizes the polynomial support as one finite rectangular
pattern, reconstructs specialized evaluation from the pattern coefficient vector, applies the
simultaneous full-rank law, and finally uses faithfulness of the coefficient vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- A polynomial-coefficient differential relation on a finite translated jet rectangle, valid on
the whole common upper domain. -/
def PolynomialCoefficientDifferentialRelationHolds
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (orders : Fin m → ℕ)
    (u : PrimeLogBoundedGauge)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X]) : Prop :=
  ∀ z : ℂ, (∀ i : Fin m, 0 < (z + shiftValue (shiftCode i)).im) →
    MvPolynomial.eval
      (primeLogDifferentialJetPacket (fun q ↦ u q)
        (fun i ↦ z + shiftValue (shiftCode i)) orders)
      (specializePolynomialCoefficients z Q) = 0

/-- **Polynomial-coefficient finite-translate freeness.** A pattern-free prime-log source admits no
nonzero `C[z]`-coefficient differential relation on any finite injective shift packet. -/
theorem polynomialCoefficientDifferentialRelation_eq_zero
    {Γ : Type*} {m : ℕ} (shiftValue : Γ → ℂ)
    (shiftCode : Fin m → Γ) (hshiftCode : Function.Injective shiftCode)
    (orders : Fin m → ℕ) (u : PrimeLogBoundedGauge)
    (hfree : CountableShiftPolynomialDifferentialFree shiftValue u)
    (Q : MvPolynomial (Σ i, Fin (orders i)) ℂ[X])
    (hrelation : PolynomialCoefficientDifferentialRelationHolds
      shiftValue shiftCode orders u Q) :
    Q = 0 := by
  let p := finitePatternOfPolynomial shiftCode hshiftCode orders Q
  let c := polynomialPatternCoefficientVector shiftCode hshiftCode orders Q
  have hpattern : PatternRelationHolds shiftValue p u c := by
    intro z hupper
    have hexpand := polynomialPatternCoefficientExpansion
      shiftCode hshiftCode orders Q z
      (primeLogDifferentialJetPacket (fun q ↦ u q)
        (fun i ↦ z + shiftValue (shiftCode i)) orders)
    dsimp [c, p, patternExpandedValue]
    have hzrel := hrelation z (by
      simpa [p, finitePatternOfPolynomial] using hupper)
    simpa only [finitePatternOfPolynomial, mul_assoc] using hexpand.trans hzrel
  have hc : ∀ b, c b = 0 := hfree p c hpattern
  exact polynomial_eq_zero_of_patternCoefficientVector_eq_zero
    shiftCode hshiftCode orders Q hc

end GaloisForLFunctions.HTGeometry
