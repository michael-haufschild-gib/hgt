import GaloisForLFunctions.RHTower.XiFormationEscapePrincipalClassLaw
import GaloisForLFunctions.RHTower.XiWardCubicReflectionLoewnerCodiagonalIncidence
import GaloisForLFunctions.RHTower.RoutePPrimitiveCollisionSubquantum
import GaloisForLFunctions.RHTower.XiWardCubicBoundaryResolventCompanionTraceNoGo
import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryQuadraticCurvature

/-!
# Direct subunit fusion of escape multiplicity and cubic capacity

The corpus has both halves of a Ferrero--Washington-shaped direct anchor.  Every strict-right Xi
copy carries one integer Kakutani escape unit, while its cubic Loewner landing costs at least
`115 / 108`.  The complete primitive Euler collision budget is strictly smaller than that same
quantum.

This module proves the exact three-organ fusion

`Euler budget < (115 / 108) * escape multiplicity <= cubic Loewner landing`.

No amplification occurs.  Exact signed source-to-completion transport, arithmetic-current to
reflection--Loewner identification, opposite-radial residue landing, and shorting already exist
elsewhere in the corpus.  The open theorem is formation strictness: after the common non-trace-class
metric is removed, the finite source cancellations must assemble into one coherent prime-mixed
primitive whose exactness witness survives completion.  Such a theorem must be proved before
divisor specialization.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Every actual strict-right Xi copy carries exactly one unsigned integer escape unit. -/
theorem xiRight_thetaKakutaniEscapeMultiplicity_eq_one
    (q : XiRightZeroCopy) :
    thetaKakutaniEscapeMultiplicity q.1 = 1 := by
  apply thetaKakutaniEscapeMultiplicity_eq_one_of_boundaryFlux_ne_zero
  intro hflux
  have hrate :=
    (thetaXiRankTwoBoundaryFlux_eq_zero_iff_centeredRate_eq_zero q.1).1 hflux
  have hline := (primeDepthBVWoldXiCenteredRate_eq_zero_iff q.1.1).1 hrate
  have hright := q.2
  rw [I_mul_xiSpectralPoint] at hright
  norm_num at hright hline
  linarith

/-- **Direct subunit escape-capacity fusion.**  For every actual strict-right Xi copy, the complete
primitive Euler capacity is smaller than one quantized escape unit, and that unit is bounded by
the copy's exact cubic Loewner landing. -/
theorem xiRight_directSubunitEscapeCapacityGap
    (q : XiRightZeroCopy) :
    routePPrimitiveCollisionCubicTraceBudget <
        (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ∧
      (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ≤
        ∫ r : ℝ in Set.Ioi 0,
          xiWardCubicReflectionLoewnerCodiagonalLanding q.1.1 r := by
  have hindex := xiRight_thetaKakutaniEscapeMultiplicity_eq_one q
  constructor
  · simpa [hindex] using routePPrimitiveCollisionCubicTraceBudget_lt_quantum
  · have hright := q.2
    rw [I_mul_xiSpectralPoint] at hright
    have hcharge :=
      xiWardCubicReflectionLoewnerCodiagonalLanding_charge_ge_quantum q.1.1 (by
        norm_num at hright ⊢
        linarith)
    simpa [hindex] using hcharge

/-- Exact capstone for the tropicalized defect-capacity theorem: a strict-right Xi copy carries
one unsigned escape unit, the complete primitive Euler budget is strictly smaller than that unit,
and the cubic Loewner landing costs at least the same unit. -/
theorem xiRight_tropicalizedDefectCapacityFusion
    (q : XiRightZeroCopy) :
    thetaKakutaniEscapeMultiplicity q.1 = 1 ∧
      routePPrimitiveCollisionCubicTraceBudget <
        (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ∧
      (115 / 108 : ℝ) * thetaKakutaniEscapeMultiplicity q.1 ≤
        ∫ r : ℝ in Set.Ioi 0,
          xiWardCubicReflectionLoewnerCodiagonalLanding q.1.1 r := by
  exact ⟨xiRight_thetaKakutaniEscapeMultiplicity_eq_one q,
    xiRight_directSubunitEscapeCapacityGap q⟩

/-! ## Formation-relative completion law -/

/-- On a singleton prime support, synchronized squarefree formation curvature is exactly
`3/8` times the squared prime logarithm. -/
theorem gammaSewnSynchronizedRecoveryQuadraticCost_singleton
    (p : Nat.Primes) :
    gammaSewnSynchronizedRecoveryQuadraticCost {p} =
      (3 / 8 : ℝ) * Real.log (p : ℝ) ^ 2 := by
  simp [gammaSewnSynchronizedRecoveryQuadraticCost]
  ring

/-- Primewise formation metric anomaly attached to a strict-right Xi copy.  This is the normalized
singleton synchronized-recovery curvature appearing before divisor specialization. -/
def xiWardCubicFormationMetricAnomalyTraceWeight
    (q : XiRightZeroCopy) (p : Nat.Primes) : ℝ :=
  (115 / (324 * (xiRightCenteredZero q).re ^ 4) : ℝ) *
    (gammaSewnSynchronizedRecoveryQuadraticCost {p} / (p : ℝ))

/-- The phase-matched companion trace is exactly the primitive cubic source weight times resonant
excess power. -/
theorem xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero_eq
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) =
      xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) *
        (((Real.log (p : ℝ) ^ 2 / (xiRightCenteredZero q).re ^ 2) : ℝ) ^ 2 - 1) := by
  rw [xiWardCubicPhaseMatchedKreinCompanionTraceWeight,
    primitive_to_strictRight_kreinCompanion_sq_eq_excess_gain,
    normSq_phaseMatched_primitiveStrictRight_resonantTransfer]
  norm_num [xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerValuationNat]

/-- Exact formation-relative completion law: formation metric anomaly is the mandatory completion
companion plus the literal primitive source charge, prime by prime. -/
theorem xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    xiWardCubicFormationMetricAnomalyTraceWeight q p =
      xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) +
        xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) := by
  have ha : 0 < (xiRightCenteredZero q).re := xiRightCenteredZero_re_pos q
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  rw [xiWardCubicFormationMetricAnomalyTraceWeight,
    gammaSewnSynchronizedRecoveryQuadraticCost_singleton,
    xiWardCubicPhaseMatchedKreinCompanionTraceWeight,
    primitive_to_strictRight_kreinCompanion_sq_eq_excess_gain,
    normSq_phaseMatched_primitiveStrictRight_resonantTransfer,
    xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero]
  norm_num [xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerValuationNat]
  field_simp [ha.ne', hp.ne', hlog.ne']
  ring

/-- Equivalent subtraction form: universal metric-anomaly cancellation leaves exactly the
unsquared primitive source charge rather than zero. -/
theorem xiWardCubicFormationMetricAnomalyTraceWeight_sub_companion_eq_source
    (q : XiRightZeroCopy) (p : Nat.Primes) :
    xiWardCubicFormationMetricAnomalyTraceWeight q p -
        xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) =
      xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) := by
  linarith [xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source q p]

/-- The depth-zero prime slice of mandatory phase-matched companion trace is not summable. -/
theorem not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero
    (q : XiRightZeroCopy) :
    ¬ Summable (fun p : Nat.Primes =>
      xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0)) := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes =>
      (115 / 1944 : ℝ) * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun p => harmonic_minorant_phaseMatchedKreinCompanionTraceWeight p q) hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (115 / 1944 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- The literal primitive source remainder remains summable after restriction to the depth-zero
prime slice. -/
theorem summable_xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero :
    Summable (fun p : Nat.Primes =>
      xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0)) :=
  summable_xiGammaEulerPrimitiveCubicLogMomentWeight.comp_injective
    (fun _ _ h => congrArg Prod.fst h)

/-- The formation metric anomaly is itself non-trace-class on the prime slice. -/
theorem not_summable_xiWardCubicFormationMetricAnomalyTraceWeight
    (q : XiRightZeroCopy) :
    ¬ Summable (xiWardCubicFormationMetricAnomalyTraceWeight q) := by
  intro hanomaly
  apply not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero q
  have hdiff := hanomaly.sub
    summable_xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero
  exact hdiff.congr fun p => by
    linarith [xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source q p]

/-- Although both formation anomaly and completion companion are non-trace-class, their exact
relative remainder is summable and retains literal primitive source provenance. -/
theorem summable_xiWardCubicFormationRelativeRemainder
    (q : XiRightZeroCopy) :
    Summable (fun p : Nat.Primes =>
      xiWardCubicFormationMetricAnomalyTraceWeight q p -
        xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0)) :=
  summable_xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero.congr fun p =>
    (xiWardCubicFormationMetricAnomalyTraceWeight_sub_companion_eq_source q p).symm

/-- Closed capstone for formation-relative completion: exact primewise anomaly subtraction, both
non-trace-class metric terms, and the summable literal source remainder. -/
theorem xiRight_tropicalizedDefectCapacityFormationRelativeCompletion
    (q : XiRightZeroCopy) :
    (∀ p : Nat.Primes,
      xiWardCubicFormationMetricAnomalyTraceWeight q p =
        xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) +
          xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0)) ∧
      ¬ Summable (fun p : Nat.Primes =>
        xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0)) ∧
      ¬ Summable (xiWardCubicFormationMetricAnomalyTraceWeight q) ∧
      Summable (fun p : Nat.Primes =>
        xiWardCubicFormationMetricAnomalyTraceWeight q p -
          xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0)) := by
  exact ⟨xiWardCubicFormationMetricAnomalyTraceWeight_eq_companion_add_source q,
    not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight_prime_zero q,
    not_summable_xiWardCubicFormationMetricAnomalyTraceWeight q,
    summable_xiWardCubicFormationRelativeRemainder q⟩

end

end RHTower
