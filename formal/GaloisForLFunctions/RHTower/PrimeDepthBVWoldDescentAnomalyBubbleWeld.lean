import GaloisForLFunctions.RHTower.PrimeDepthBVWoldRelationKernelAtlasTransition
import GaloisForLFunctions.RHTower.XiSourceMatchedChargedBubble

/-!
# Scalar-descent anomaly and source-matched Ward bubbles

The graded-`det₂` anomaly on every prime/depth triangle has a canonical positive logarithmic
scale. Dividing its logarithm by that scale recovers the signed transverse Xi source rate,
independently of the chosen prime and depth. Its absolute value is exactly the Route-R completion
core radius, and analytic multiplicity converts it into the conserved Noether charge.

Consequently every source-matched escaping Ward bubble carries the same normalized descent
action. Functional-equation reflection cancels signed anomaly automatically, but preserves this
positive action and hence cannot remove an off-line defect.
-/

open Complex Filter MeasureTheory Real Set
open scoped Differential Topology

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Signed scalar-descent anomaly after removing the positive prime/depth chart scale. -/
def primeDepthBVWoldXiNormalizedLogDescentAnomaly
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.log (primeDepthBVWoldPrimeConsecutiveTriangleAnomaly
      (primeDepthBVWoldXiCenteredRate rho) p e) /
    primeDepthBVWoldPrimeConsecutiveTriangleLogScale p e

/-- Every prime/depth anomaly chart recovers the same signed transverse source rate. -/
theorem primeDepthBVWoldXiNormalizedLogDescentAnomaly_eq_centeredRate
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldXiNormalizedLogDescentAnomaly rho p e =
      primeDepthBVWoldXiCenteredRate rho := by
  rw [primeDepthBVWoldXiNormalizedLogDescentAnomaly,
    primeDepthBVWoldXiCenteredRate,
    log_primeDepthBVWoldPrimeConsecutiveTriangleAnomaly]
  field_simp [ne_of_gt
    (primeDepthBVWoldPrimeConsecutiveTriangleLogScale_pos p e)]

/-- Functional-equation reflection cancels the signed normalized anomaly. -/
theorem primeDepthBVWoldXiNormalizedLogDescentAnomaly_reflection
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldXiNormalizedLogDescentAnomaly
        (xiZeroLineConjEquiv rho) p e =
      -primeDepthBVWoldXiNormalizedLogDescentAnomaly rho p e := by
  rw [primeDepthBVWoldXiNormalizedLogDescentAnomaly_eq_centeredRate,
    primeDepthBVWoldXiNormalizedLogDescentAnomaly_eq_centeredRate,
    primeDepthBVWoldXiCenteredRate_reflection]

/-- Positive action retained after forgetting anomaly orientation. -/
def primeDepthBVWoldXiDescentAnomalyAction
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) : ℝ :=
  |primeDepthBVWoldXiNormalizedLogDescentAnomaly rho p e|

theorem primeDepthBVWoldXiDescentAnomalyAction_eq_abs_centeredRate
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldXiDescentAnomalyAction rho p e =
      |primeDepthBVWoldXiCenteredRate rho| := by
  rw [primeDepthBVWoldXiDescentAnomalyAction,
    primeDepthBVWoldXiNormalizedLogDescentAnomaly_eq_centeredRate]

/-- Unlike signed holonomy, anomaly action is invariant under reflection. -/
theorem primeDepthBVWoldXiDescentAnomalyAction_reflection
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldXiDescentAnomalyAction (xiZeroLineConjEquiv rho) p e =
      primeDepthBVWoldXiDescentAnomalyAction rho p e := by
  change
    |primeDepthBVWoldXiNormalizedLogDescentAnomaly
        (xiZeroLineConjEquiv rho) p e| =
      |primeDepthBVWoldXiNormalizedLogDescentAnomaly rho p e|
  rw [primeDepthBVWoldXiNormalizedLogDescentAnomaly_reflection, abs_neg]

/-- Canonically normalized scalar-descent anomaly is exactly the completion-core radius. -/
theorem primeDepthBVWoldXiDescentAnomalyAction_eq_resolutionCoreRadius
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    primeDepthBVWoldXiDescentAnomalyAction rho p e =
      routeRPrimeGammaXiResolutionCoreRadius rho := by
  rw [primeDepthBVWoldXiDescentAnomalyAction_eq_abs_centeredRate,
    routeRPrimeGammaXiResolutionCoreRadius_eq_abs_sourceCayleyTransverseRate,
    sourceCayleyTransverseRate_one_eq_centeredGrade,
    primeDepthBVWoldXiCenteredRate]

/-- Multiplicity converts normalized scalar-descent action into conserved Noether charge. -/
theorem abs_routeRPrimeGammaXiNoetherOrientationCharge_eq_descentAnomalyAction
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ) :
    |routeRPrimeGammaXiNoetherOrientationCharge rho| =
      ((analyticOrderAt xi (rho : ℂ)).toNat : ℝ) / 2 *
        primeDepthBVWoldXiDescentAnomalyAction rho p e := by
  rw [abs_routeRPrimeGammaXiNoetherOrientationCharge_eq,
    primeDepthBVWoldXiDescentAnomalyAction_eq_resolutionCoreRadius]

/-- Every member of the escaping bubble sequence carries the same renormalized descent action. -/
theorem abs_centeredCharge_quartetPoint_eq_descentAnomalyAction
    (rho : XiDivisorSupport) (p : Nat.Primes) (e n : ℕ) :
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    |(-((quartetPoint (xiDivisorBubbleDisplacement rho)
          (escapingQuartetHeight n) - 1 / 2) * (m : ℂ))).re| =
      (m : ℝ) / 2 * primeDepthBVWoldXiDescentAnomalyAction rho p e := by
  dsimp only
  rw [abs_centeredCharge_quartetPoint_xiDivisorBubbleDisplacement,
    abs_routeRPrimeGammaXiNoetherOrientationCharge_eq_descentAnomalyAction]

/-- Signed reflection balance is automatic, but positive action cancels only on the critical line. -/
theorem primeDepthBVWoldXiDescentAnomaly_reflectionFalsification
    (rho : XiDivisorSupport) (p : Nat.Primes) (e : ℕ)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    primeDepthBVWoldXiNormalizedLogDescentAnomaly rho p e +
        primeDepthBVWoldXiNormalizedLogDescentAnomaly
          (xiZeroLineConjEquiv rho) p e = 0 ∧
      0 < primeDepthBVWoldXiDescentAnomalyAction rho p e +
        primeDepthBVWoldXiDescentAnomalyAction
          (xiZeroLineConjEquiv rho) p e := by
  constructor
  · rw [primeDepthBVWoldXiNormalizedLogDescentAnomaly_reflection]
    ring
  · rw [primeDepthBVWoldXiDescentAnomalyAction_reflection]
    have hpos : 0 < primeDepthBVWoldXiDescentAnomalyAction rho p e := by
      rw [primeDepthBVWoldXiDescentAnomalyAction_eq_abs_centeredRate, abs_pos]
      exact fun hzero =>
        hoff ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp hzero)
    linarith

/-- An off-line Xi divisor is simultaneously a nonzero normalized descent anomaly and a
source-matched escaping Ward bubble with the same multiplicity-calibrated charge. -/
theorem offLineXiDivisor_descentAnomalyBubbleLaw
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2)
    (p : Nat.Primes) (e : ℕ) :
    let m := (analyticOrderAt xi (rho : ℂ)).toNat
    0 < primeDepthBVWoldXiDescentAnomalyAction rho p e ∧
    (∀ n,
      |(-((quartetPoint (xiDivisorBubbleDisplacement rho)
          (escapingQuartetHeight n) - 1 / 2) * (m : ℂ))).re| =
        (m : ℝ) / 2 * primeDepthBVWoldXiDescentAnomalyAction rho p e) ∧
    (∀ n, multiplicityEscapingQuartetWardMass
      (xiDivisorBubbleDisplacement rho) m n =
        m • ENNReal.ofReal (8 * π)) := by
  dsimp only
  have hescape := offLineXiDivisor_sourceMatchedChargedBubble rho hoff
  dsimp only at hescape
  refine ⟨?_, abs_centeredCharge_quartetPoint_eq_descentAnomalyAction rho p e,
    hescape.2.2.2.2.1⟩
  rw [primeDepthBVWoldXiDescentAnomalyAction_eq_abs_centeredRate, abs_pos]
  exact fun hzero =>
    hoff ((primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp hzero)

end

end RHTower
