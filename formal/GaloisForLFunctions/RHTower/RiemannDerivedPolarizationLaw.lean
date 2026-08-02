import GaloisForLFunctions.HTGeometry.DerivedPolarizationLaw
import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHodge
import GaloisForLFunctions.RHTower.PurityCurvatureExponentialTransgression
import GaloisForLFunctions.RHTower.XiSourceEntropyCauchyTomography

/-!
# Riemann derived-polarization law

The oriented divisor cup, its positive odd Hodge polarization, Frobenius
weight law, reflected source entropy, and prime-valuation Rees type are
different representations of one commutator curvature.

The global metric defect is the cup pairing against the Frobenius--Hodge
commutator.  Orbitwise, that commutator is multiplication by the weight-one
purity curvature.  The same curvature is reflected arithmetic source entropy,
and its sign is exactly the finite-Rees/all-orders-flat type split.  Exact
weight-one conservation is equivalent to the Riemann hypothesis.
-/

open Complex

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Hermitian metric obtained by composing the oriented divisor cup with its
odd Hodge operator. -/
def deningerArithmeticDerivedHodgeMetric
    (a b : DeningerArithmeticGradedH1) : ℂ :=
  cupHodgeMetric deningerArithmeticGradedOrientedCup
    deningerArithmeticGradedOrientedHodge.sigma a b

/-- The failure of Frobenius to satisfy the weight-one Hermitian law is
exactly its cup pairing against the Hodge commutator. -/
theorem deningerArithmeticDerivedHodgeMetric_purityDefect
    (a b : DeningerArithmeticGradedH1) :
    deningerArithmeticDerivedHodgeMetric
          (deningerArithmeticGradedTheta a) b +
        deningerArithmeticDerivedHodgeMetric a
          (deningerArithmeticGradedTheta b) -
        deningerArithmeticDerivedHodgeMetric a b =
      -deningerArithmeticGradedOrientedCup a
        (deningerArithmeticGradedTheta
            (deningerArithmeticGradedOrientedHodge.sigma b) -
          deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedTheta b)) := by
  simpa [deningerArithmeticDerivedHodgeMetric, cupHodgeCommutator] using
    cupHodgeMetric_purityDefect
      deningerArithmeticGradedOrientedCup
      deningerArithmeticGradedTheta
      deningerArithmeticGradedOrientedHodge.sigma
      1 (fun x z => by
        simpa using deningerArithmeticGradedTheta_orientedCup x z) a b

/-- Exact weight-one conservation of the derived Hodge metric is equivalent
to the Riemann hypothesis. -/
theorem deningerArithmeticDerivedHodgeMetric_weightOne_iff_riemannHypothesis :
    (∀ a b : DeningerArithmeticGradedH1,
      deningerArithmeticDerivedHodgeMetric
            (deningerArithmeticGradedTheta a) b +
          deningerArithmeticDerivedHodgeMetric a
            (deningerArithmeticGradedTheta b) =
        deningerArithmeticDerivedHodgeMetric a b) ↔
      RiemannHypothesis := by
  calc
    (∀ a b : DeningerArithmeticGradedH1,
      deningerArithmeticDerivedHodgeMetric
            (deningerArithmeticGradedTheta a) b +
          deningerArithmeticDerivedHodgeMetric a
            (deningerArithmeticGradedTheta b) =
        deningerArithmeticDerivedHodgeMetric a b) ↔
        ∀ a b : DeningerArithmeticGradedH1,
          cupHodgeMetric deningerArithmeticGradedOrientedCup
                deningerArithmeticGradedOrientedHodge.sigma
                (deningerArithmeticGradedTheta a) b +
              cupHodgeMetric deningerArithmeticGradedOrientedCup
                deningerArithmeticGradedOrientedHodge.sigma
                a (deningerArithmeticGradedTheta b) =
            1 * cupHodgeMetric deningerArithmeticGradedOrientedCup
              deningerArithmeticGradedOrientedHodge.sigma a b := by
                simp [deningerArithmeticDerivedHodgeMetric]
    _ ↔ ∀ b : DeningerArithmeticGradedH1,
        deningerArithmeticGradedTheta
            (deningerArithmeticGradedOrientedHodge.sigma b) =
          deningerArithmeticGradedOrientedHodge.sigma
            (deningerArithmeticGradedTheta b) :=
      cupHodgeMetric_weightLaw_iff_commutes
        deningerArithmeticGradedOrientedCup
        deningerArithmeticGradedTheta
        deningerArithmeticGradedOrientedHodge.sigma
        1 (fun x z => by
          simpa using deningerArithmeticGradedTheta_orientedCup x z)
        deningerArithmeticGradedOrientedCup_nondegenerate
    _ ↔ RiemannHypothesis :=
      deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis

/-- Orbitwise Hodge-commutator coefficient is the negative weight-one purity
curvature of the corresponding Xi divisor point. -/
theorem deningerArithmeticOrientedHodge_commutator_apply_eq_purityCurvature
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) -
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a)) q =
      -weightOnePurityCurvature (q.1 : ℂ) *
        deningerArithmeticGradedOrientedHodge.sigma a q := by
  change
    deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) q -
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a) q =
      _
  rw [deningerArithmeticGradedTheta_orientedHodge_defect,
    deningerArithmeticGradedOrientedHodge_apply]
  simp only [weightOnePurityCurvature, deningerDivisorThetaEigen]
  rw [show ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) by
    rfl]
  simp only [map_sub, map_one]
  ring

/-- Reflected source entropy is the real form of weight-one purity
curvature. -/
theorem weightOnePurityCurvature_eq_reflectedSourceEntropy
    (s : ℂ) :
    weightOnePurityCurvature s =
      (riemannReflectedSourceEntropy s : ℂ) := by
  rw [riemannReflectedSourceEntropy_eq_neg_sourceCayleyRate]
  simp only [weightOnePurityCurvature,
    sourceCayleyTransverseRate, sub_re, one_re, ofReal_neg]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Inside the critical strip, negative purity curvature is exactly the
all-orders-flat prime-valuation Rees sector. -/
theorem weightOnePurityCurvature_selects_primeValuationReesType
    (s : ℂ) (hstrip : 0 < s.re ∧ s.re < 1) :
    ReesAllOrdersFlat Filter.atTop
        GaloisForLFunctions.primeWoldBoundaryVolumeBelow
        (primeValuationSquaredHellingerBelow (s.re - 1 / 2)) ↔
      (weightOnePurityCurvature s).re < 0 := by
  rw [riemannSourceEntropy_selects_primeValuationReesType s hstrip,
    weightOnePurityCurvature_eq_reflectedSourceEntropy]
  simp

end

end RHTower
