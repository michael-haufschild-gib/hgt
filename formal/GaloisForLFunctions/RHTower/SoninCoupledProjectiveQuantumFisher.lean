import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue
import GaloisForLFunctions.RHTower.SoninCoupledVacuumFeshbach

/-!
# Coupled Sonin projective quantum-Fisher reduction

The vacuum-Feshbach source interface currently permits an aperture-dependent scalar counterterm
`c`.  Pure-state projective quantum geometry replaces that choice by the invariant two-vector
Gram value

```text
D_a(p) = ||V_a(1)||^2 ||V_a(p)||^2 - |<V_a(1),V_a(p)>|^2.
```

This is the unnormalised Fubini--Study tangent energy.  It is nonnegative before any comparison
with the prime--Gamma target and is unchanged when a scalar multiple of the vacuum direction is
added to the tangent.  The resulting RH interface contains only the aperture choice: the scalar
counterterm has disappeared.

The remaining analytic input is still a source comparison.  No positivity of the target moment
functional is assumed or hidden in the definition.
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Gauge-invariant projective tangent energy between the coupled vacuum column and one actual
coupled polynomial source vector. -/
def soninAllPrimeCoupledProjectiveTangentEnergy
    (a : SoninPositiveAperture) (p : Polynomial ℝ) : ℝ :=
  HTGeometry.projectiveGramTangentEnergy
    (𝕜 := ℂ)
    (soninAllPrimeCoupledPowerVector a 0)
    (soninAllPrimeCoupledPolynomialPowerVector a p)

/-- The source projective tangent energy is structurally nonnegative by Hilbert-space
Cauchy--Schwarz; no arithmetic sign hypothesis is required. -/
theorem soninAllPrimeCoupledProjectiveTangentEnergy_nonneg
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    0 ≤ soninAllPrimeCoupledProjectiveTangentEnergy a p := by
  exact HTGeometry.projectiveGramTangentEnergy_nonneg (𝕜 := ℂ) _ _

/-- Normalized pure-state quantum Fisher value of the coupled polynomial tangent.  The
normalization uses the same zeroth source energy that canonically normalizes the coupled route. -/
def soninAllPrimeCoupledPureStateQuantumFisherValue
    (a : SoninPositiveAperture) (p : Polynomial ℝ) : ℝ :=
  4 * soninAllPrimeCoupledProjectiveTangentEnergy a p /
    (soninAllPrimeCoupledTraceMoment a 0).re ^ 2

/-- Every coupled pure-state quantum Fisher value is nonnegative. -/
theorem soninAllPrimeCoupledPureStateQuantumFisherValue_nonneg
    (a : SoninPositiveAperture) (p : Polynomial ℝ) :
    0 ≤ soninAllPrimeCoupledPureStateQuantumFisherValue a p := by
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (soninAllPrimeCoupledProjectiveTangentEnergy_nonneg a p))
    (sq_nonneg _)

/-- **Counterterm-free projective-Fisher source comparison.**  For each zero-constant integer
tail, compare its gauge-invariant coupled projective tangent energy with the target vacuum
Feshbach remainder.  Canonical normalization has been cross-multiplied, so no quotient or scalar
counterterm remains. -/
def SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 *
            soninAllPrimeCoupledProjectiveTangentEnergy a.1
              (q.map (Int.castRingHom ℝ)) ≤
          (HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2

/-- The projective-Fisher comparison forces every target vacuum Feshbach remainder to be
nonnegative.  The contradiction uses only structural source Gram positivity and concrete source
nondegeneracy. -/
theorem primeArchVacuumFeshbachIntNonnegative_of_soninCoupledProjectiveFisher
    (h : SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound) :
    PrimeArchVacuumFeshbachIntNonnegative := by
  intro q hq
  let target : ℝ :=
    HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
      (q.map (Int.castRingHom ℝ))
  by_contra htarget
  have htargetNeg : target < 0 := lt_of_not_ge htarget
  let ε : ℝ := -target / 2
  have hε : 0 < ε := by
    dsimp only [ε]
    linarith
  obtain ⟨a, ha⟩ := h q hq ε hε
  have hmass : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re :=
    (soninAllPrimeCoupledTraceMoment_zero_re_pos_iff_column_ne_zero a.1).2 a.2
  have hmassSq : 0 < (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2 :=
    sq_pos_of_pos hmass
  have htargetε : target + ε < 0 := by
    dsimp only [ε]
    linarith
  have hright :
      (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2 < 0 :=
    mul_neg_of_neg_of_pos htargetε hmassSq
  have hleft :
      0 ≤ normalizedPrimeArchMoment 0 *
        soninAllPrimeCoupledProjectiveTangentEnergy a.1
          (q.map (Int.castRingHom ℝ)) :=
    mul_nonneg normalizedPrimeArchMoment_zero_pos.le
      (soninAllPrimeCoupledProjectiveTangentEnergy_nonneg _ _)
  change normalizedPrimeArchMoment 0 *
      soninAllPrimeCoupledProjectiveTangentEnergy a.1
        (q.map (Int.castRingHom ℝ)) ≤
    (target + ε) * (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2 at ha
  linarith

/-- **Projective quantum-Fisher coupled-Sonin RH capstone.**  The new source obligation has one
choice per test (the aperture) rather than the aperture-plus-counterterm pair of the Mori/Feshbach
interface. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumProjectiveFisherUpperBound
    (h : SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound) :
    RiemannHypothesis :=
  primeArchVacuumFeshbachIntNonnegative_iff_riemannHypothesis.mp
    (primeArchVacuumFeshbachIntNonnegative_of_soninCoupledProjectiveFisher h)

/-- Fully quotient-free Robertson form of the counterterm-free projective comparison. -/
def SoninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound : Prop :=
  ∀ (q : Polynomial ℤ), q.coeff 0 = 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ a : SoninCoupledNondegenerateAperture,
        normalizedPrimeArchMoment 0 ^ 2 *
            soninAllPrimeCoupledProjectiveTangentEnergy a.1
              (q.map (Int.castRingHom ℝ)) ≤
          (HTGeometry.momentVacuumRobertsonDeterminant normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2

/-- The quotient-free Robertson projective comparison implies the Feshbach form by rescaling the
positive error with the target vacuum mass. -/
theorem soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_of_robertson
    (h : SoninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound) :
    SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound := by
  intro q hq ε hε
  let δ : ℝ := normalizedPrimeArchMoment 0 * ε
  have hδ : 0 < δ := mul_pos normalizedPrimeArchMoment_zero_pos hε
  obtain ⟨a, ha⟩ := h q hq δ hδ
  refine ⟨a, ?_⟩
  have hscaled :
      normalizedPrimeArchMoment 0 *
          (normalizedPrimeArchMoment 0 *
            soninAllPrimeCoupledProjectiveTangentEnergy a.1
              (q.map (Int.castRingHom ℝ))) ≤
        normalizedPrimeArchMoment 0 *
          ((HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2) := by
    calc
      normalizedPrimeArchMoment 0 *
          (normalizedPrimeArchMoment 0 *
            soninAllPrimeCoupledProjectiveTangentEnergy a.1
              (q.map (Int.castRingHom ℝ))) =
          normalizedPrimeArchMoment 0 ^ 2 *
            soninAllPrimeCoupledProjectiveTangentEnergy a.1
              (q.map (Int.castRingHom ℝ)) := by ring
      _ ≤ (HTGeometry.momentVacuumRobertsonDeterminant normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + δ) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2 := ha
      _ = normalizedPrimeArchMoment 0 *
          ((HTGeometry.momentVacuumFeshbachRemainder normalizedPrimeArchMoment
              (q.map (Int.castRingHom ℝ)) + ε) *
            (soninAllPrimeCoupledTraceMoment a.1 0).re ^ 2) := by
        rw [HTGeometry.momentVacuumRobertsonDeterminant_eq_mul_feshbach
          normalizedPrimeArchMoment normalizedPrimeArchMoment_zero_pos.ne']
        dsimp only [δ]
        ring
  exact (mul_le_mul_iff_of_pos_left normalizedPrimeArchMoment_zero_pos).mp hscaled

/-- Quotient-free projective Robertson comparison also proves RH. -/
theorem riemannHypothesis_of_soninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound
    (h : SoninCoupledPrimeArchVacuumProjectiveRobertsonUpperBound) :
    RiemannHypothesis :=
  riemannHypothesis_of_soninCoupledPrimeArchVacuumProjectiveFisherUpperBound
    (soninCoupledPrimeArchVacuumProjectiveFisherUpperBound_of_robertson h)

end

end RHTower
