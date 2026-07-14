import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase
import GaloisForLFunctions.RHTower.PrimeArchBernsteinDirichletDissipation
import GaloisForLFunctions.RHTower.PrimeArchBernsteinExactExponentialThreshold

/-!
# Narrow-sector Bernstein dissipation master theorem

This module joins three statements about the same endpoint prime--archimedean Bernstein source:
the exact narrow-sector ceiling, the cancellation-resistant purity dichotomy, and the exact
degree-elevation Dirichlet balance.  No auxiliary carrier or alternate RH route is introduced.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The exact exponential exponent of initial energy plus cumulative Bernstein dissipation. -/
def PrimeArchEndpointBernsteinCumulativeDissipationExactExponentialExponent
    (E : ℝ) : Prop :=
  ExactExponentialExponentAtNatInfinity
    primeArchEndpointBernsteinCumulativeDissipationEnergy E

/-- Purity and cumulative dissipation have exactly the same exponential exponent. -/
theorem primeArchEndpointBernsteinCumulativeDissipationExactExponent_iff_purity
    (E : ℝ) :
    PrimeArchEndpointBernsteinCumulativeDissipationExactExponentialExponent E ↔
      PrimeArchEndpointBernsteinExactExponentialExponent E := by
  change ExactExponentialExponentAtNatInfinity
      primeArchEndpointBernsteinCumulativeDissipationEnergy E ↔
    ExactExponentialExponentAtNatInfinity primeArchEndpointBernsteinPurity E
  have hfun : primeArchEndpointBernsteinCumulativeDissipationEnergy =
      fun n : ℕ => (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := by
    funext n
    exact primeArchEndpointBernsteinCumulativeDissipationEnergy_eq_scaledPurity n
  rw [hfun]
  exact exactExponentialExponentAtNatInfinity_natCast_add_one_mul_iff
    primeArchEndpointBernsteinPurity
    (fun n => bernsteinCoefficientPurity_nonneg _ n) E

/-- The unique narrow-sector exponent is common to purity and cumulative dissipation. -/
theorem existsUnique_primeArchEndpointBernsteinPurityDissipationExactExponent :
    ∃! E : ℝ,
      1 ≤ E ∧
      E < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
      PrimeArchEndpointBernsteinExactExponentialExponent E ∧
      PrimeArchEndpointBernsteinCumulativeDissipationExactExponentialExponent E ∧
      (RiemannHypothesis ↔ E = 1) := by
  obtain ⟨E, hE, hunique⟩ :=
    existsUnique_primeArchEndpointBernsteinExactExponentialExponent
  refine ⟨E, ⟨hE.1, hE.2.1, hE.2.2.1,
    (primeArchEndpointBernsteinCumulativeDissipationExactExponent_iff_purity E).2 hE.2.2.1,
    hE.2.2.2⟩, ?_⟩
  intro F hF
  exact hunique F ⟨hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.2⟩

/-- **Narrow-sector dissipation master theorem.**  Purity and cumulative dissipation share one
unique exact exponent in the universal narrow chamber.  RH is exactly its critical value one and
the cofinally linearly dissipative phase; false RH makes the common exponent source-attained and
forces simultaneous purity and mean-dissipation divergence. -/
theorem primeArchBernsteinNarrowSectorDissipationMaster :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 251001 / 250000 ∧
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 201 / 200 ∧
    (∀ n : ℕ,
      normalizedPrimeArchMoment 0 ^ 2 ≤
          (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n ∧
        primeArchEndpointBernsteinPurity n ≤
          (xiReciprocalSquareAbsoluteMass *
            xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2) ∧
    (RiemannHypothesis ↔
      PrimeArchEndpointBernsteinPurityCofinallyBounded) ∧
    (RiemannHypothesis ↔
      PrimeArchEndpointBernsteinCofinalLinearDissipation) ∧
    (∃! E : ℝ,
      1 ≤ E ∧
      E < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
      PrimeArchEndpointBernsteinExactExponentialExponent E ∧
      PrimeArchEndpointBernsteinCumulativeDissipationExactExponentialExponent E ∧
      (RiemannHypothesis ↔ E = 1)) ∧
    ((RiemannHypothesis ∧
        ∀ n : ℕ,
          primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2) ∨
      (¬ RiemannHypothesis ∧
        Tendsto primeArchEndpointBernsteinPurity atTop atTop ∧
        Tendsto primeArchEndpointBernsteinMeanDissipation atTop atTop ∧
        ∃ B : ℝ, PrimeArchEndpointBernsteinAttainedExactThreshold B)) := by
  refine ⟨xiSectorConfinedBernsteinAmplitudeBase_sq_eq,
    xiSectorConfinedBernsteinAmplitudeBase_sq_lt_twoHundredOne_over_twoHundred,
    fun n => ⟨mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n,
      primeArchEndpointBernsteinPurity_le_sectorConfined n⟩,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded,
    riemannHypothesis_iff_primeArchEndpointBernsteinCofinalLinearDissipation,
    existsUnique_primeArchEndpointBernsteinPurityDissipationExactExponent, ?_⟩
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH,
      primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH⟩
  · exact Or.inr ⟨hRH,
      tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH,
      tendsto_primeArchEndpointBernsteinMeanDissipation_atTop_of_not_rh hRH,
      exists_primeArchEndpointBernsteinAttainedExactThreshold_of_not_rh hRH⟩

end

end RHTower
