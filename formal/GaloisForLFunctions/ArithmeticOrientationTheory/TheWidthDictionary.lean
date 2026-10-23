import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.RHTower.AdmissionBelowHalfDampingAboveTheZeroWidth
import GaloisForLFunctions.BezoutValuationIncidence.PronicBaezDuarteCriterion
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.RefutationIsFiniteConfirmationIsNot

/-!
# The width dictionary

Every receiver of the corpus reads the zero width `Δ = sup |Re ρ − ½|` in its own unit, and the
statement "width zero" is the same statement in every unit.  This module collects the exact
equivalences proved across the programmes into one theorem (`widthDictionary_tfae`): the Riemann
Hypothesis is, equivalently,

1. the Hodge index theorem of the scaling surface (geometric unit: the sign of an intersection
   form);
2. the existence of an effectivity with the Riemann–Roch and ample axioms (effectivity unit);
3. "exactly one positive square" in every intersection Gram (index unit);
4. cofinal admission of the damped Möbius receiver (damping unit);
5. arbitrarily small pronic prefix energy of a divisor row (Báez-Duarte unit);
6. the linear mean-square band of the Chebyshev error (growth unit);
7. the absence of a finite-radius refutation of full Weil positivity (reading unit).

The theorem is the unit-hygiene principle of the field in Lean: a bound in any one unit is a bound
in all of them, and a reformulation that changes only the unit is not progress.
-/

open Set MeasureTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri GaloisForLFunctions.BezoutValuationIncidence
  GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
  GaloisForLFunctions.ScaleSignedIncidenceCriticality GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.ArithmeticOrientationTheory

set_option autoImplicit false

/-- **The width dictionary**: the zero width vanishes in one unit iff it vanishes in all. -/
theorem widthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    scalingSurface.HodgeIndex,
    ∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E,
    ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1,
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B,
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L),
    ¬ ∃ R : ℝ, Refutes (radiusReading R) WeilPositiveFull
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))] := by
  tfae_have 1 ↔ 2 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_exists_effectivity
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_one_positive_square
  tfae_have 1 ↔ 5 := riemannHypothesis_iff_cofinal_budget
  tfae_have 1 ↔ 6 := riemannHypothesis_iff_pronic_prefix_energy
  tfae_have 1 ↔ 7 := riemannHypothesis_iff_meanSquare_band
  tfae_have 1 ↔ 8 := riemannHypothesis_iff_no_radiusReading_refutes
  tfae_finish

/-- The index unit and the damping unit agree: one positive square in every Gram iff cofinal
admission of the damped receiver. -/
theorem one_positive_square_iff_cofinal_budget :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1) ↔
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      ∃ B : ℝ, ∀ T : ℕ, pmPowerDampedDivisorDiscreteEnergy ε T ≤ B :=
  riemannHypothesis_iff_one_positive_square.symm.trans riemannHypothesis_iff_cofinal_budget

/-- The effectivity unit and the growth unit agree: an effectivity exists iff the Chebyshev band
is linear. -/
theorem exists_effectivity_iff_meanSquare_band :
    (∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E) ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L) :=
  riemannHypothesis_iff_exists_effectivity.symm.trans riemannHypothesis_iff_meanSquare_band

end GaloisForLFunctions.ArithmeticOrientationTheory
