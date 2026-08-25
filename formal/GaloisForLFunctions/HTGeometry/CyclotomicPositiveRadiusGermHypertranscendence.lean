import GaloisForLFunctions.HTGeometry.CyclotomicNumberFieldTailFreedom

/-!
# Positive-radius cyclotomic germ hypertranscendence

A coefficient sequence defines a hypertranscendental convergent germ when its scalar formal power
series has nonzero convergence radius and no nonzero differential polynomial vanishes after formal
jet substitution.  Algebraic logarithmic profiles bounded below linearly have this property for
every algebraic unit-modulus phase sequence with bounded-total-degree tail freedom.

The canonical sequence of odd prime-order roots of unity supplies a closed, unconditional endpoint.
-/

open Filter PowerSeries MvPolynomial
open scoped ENNReal Topology

namespace GaloisForLFunctions

noncomputable section

/-- A convergent characteristic-zero power-series germ satisfying no algebraic differential
equation.  Formal Taylor expansion is faithful for convergent complex germs, so the second conjunct
is the exact formal-jet realization of analytic germ hypertranscendence. -/
def ConvergentPowerSeriesGermHypertranscendental (a : ℕ → ℂ) : Prop :=
  (FormalMultilinearSeries.ofScalars ℂ a).radius ≠ 0 ∧
    ∀ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 →
      MvPolynomial.aeval
        (formalJets n (PowerSeries.mk a)) P ≠ 0

/-- Every algebraic logarithmic profile with an eventual linear lower bound produces a
hypertranscendental convergent germ for the phase sequence `u`. -/
def AlgebraicLowerBoundedLogProfileGermHTLaw (u : ℕ → ℂ) : Prop :=
  ∀ b : ℕ → ℝ,
    (∀ n, IsAlgebraic ℚ (b n)) →
    (∃ c : ℝ, ∀ᶠ n in atTop, c ≤ b n / (n : ℝ)) →
    ConvergentPowerSeriesGermHypertranscendental
      (boundedRelationExponentialCoeff b u)

/-- Bounded-total-degree phase-tail freedom converts any algebraic, linearly lower-bounded
logarithmic profile into a hypertranscendental convergent germ. -/
theorem algebraicLowerBoundedLogProfileGermHTLaw_of_phaseTailFreedom
    {u : ℕ → ℂ}
    (htail : BoundedTotalDegreeTailFreedom u)
    (huAlg : ∀ n, IsAlgebraic ℚ (u n))
    (huNorm : ∀ n, ‖u n‖ = 1) :
    AlgebraicLowerBoundedLogProfileGermHTLaw u := by
  intro b hbAlg hlower
  constructor
  · exact phaseTailExponentialSeries_radius_ne_zero_of_eventually_ratio_ge
      hlower huNorm
  · intro n P hP
    refine no_formal_relation_of_phaseTail_exponential
      (F := PowerSeries.mk (boundedRelationExponentialCoeff b u))
      (b := b) (u := u) ?_ hbAlg htail huAlg huNorm P hP
    intro i
    simp [boundedRelationExponentialCoeff]

theorem canonicalOddPrimePhase_isAlgebraic (n : ℕ) :
    IsAlgebraic ℚ (canonicalOddPrimePhase n) :=
  HTGeometry.primitiveRoot_isAlgebraic (canonicalOddPrimeOrder_prime n).pos
    (canonicalOddPrimePhase_isPrimitiveRoot n)

theorem canonicalOddPrimePhase_norm (n : ℕ) :
    ‖canonicalOddPrimePhase n‖ = 1 :=
  HTGeometry.norm_eq_one_of_isPrimitiveRoot_complex
    (canonicalOddPrimeOrder_prime n).pos
    (canonicalOddPrimePhase_isPrimitiveRoot n)

/-- Closed positive-radius germ theorem for the canonical odd-prime cyclotomic phase sequence. -/
theorem canonicalOddPrimePhase_algebraicLowerBoundedLogProfileGermHTLaw :
    AlgebraicLowerBoundedLogProfileGermHTLaw canonicalOddPrimePhase :=
  algebraicLowerBoundedLogProfileGermHTLaw_of_phaseTailFreedom
    canonicalOddPrimePhase_boundedTotalDegreeTailFreedom
    canonicalOddPrimePhase_isAlgebraic canonicalOddPrimePhase_norm

end
end GaloisForLFunctions
