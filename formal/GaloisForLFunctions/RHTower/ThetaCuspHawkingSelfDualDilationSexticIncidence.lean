import GaloisForLFunctions.RHTower.ThetaCuspHawkingSelfDualEinsteinDilationCarrier
import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySexticMemoryTriplePole

/-!
# Self-dual Hawking carrier and sextic Teukolsky incidence

Conjugating the normalized self-dual Hawking dilation coefficient gives the anti-self-dual
charge-minus-two carrier. Two neutral horizon-mass insertions dress this carrier to the first
sextic charge-decay rung. Its three-Green principal coefficient is

`C_-(z) * 2 conj(A)^(2 : ℕ) M(A,z)^(2 : ℕ) / J'(omega_3)^(3 : ℕ)`.

Every factor is nonzero at an Xi divisor when `A != 0`. Multiplication by `C_-(z)` preserves the
triple-pole limit, so continuous one- and two-Green completions cannot cancel it. Exact
Birmingham--Mokhtari frequency incidence with third negative-branch overtone is equivalent to
zero Xi tilt.

This is the closed chiral Einstein sector. Additional non-self-dual terms with same three-Green
grade require separate full-source analysis.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

def d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient (z : ℂ) : ℂ :=
  starRingEnd ℂ
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 z)

theorem d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient_xi_ne_zero
    (q : XiZeroCopy) :
    d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient
      (xiSpectralPoint q) ≠ 0 := by
  unfold d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient
  exact (map_ne_zero (starRingEnd ℂ)).2
    (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero
      (by norm_num) q)

def d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient
    (amplitude z : ℂ) : ℂ :=
  d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient z *
    d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient amplitude z

theorem d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient_xi_ne_zero_iff
    (amplitude : ℂ) (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0 ↔ amplitude ≠ 0 := by
  constructor
  · intro h ha
    rw [ha] at h
    simp [d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient,
      d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient] at h
  · intro ha
    exact mul_ne_zero
      (d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient_xi_ne_zero q)
      ((d4ThetaHawkingSexticRepeatedMemoryTriplePoleCoefficient_xi_ne_zero_iff
        amplitude q).2 ha)

def d4ThetaHawkingSelfDualSeededSexticCompletion
    (amplitude z : ℂ) (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (omega : ℂ) : ℂ :=
  d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient z *
    d4ThetaHawkingSexticRepeatedMemoryCompletion amplitude z
      twoGreenNumerator oneGreenNumerator omega

theorem d4ThetaHawkingSelfDualSeededSexticCompletion_tendsto_triplePoleCoefficient
    (amplitude : ℂ) (q : XiZeroCopy)
    (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (hN2 : ContinuousAt twoGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
    (hN1 : ContinuousAt oneGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))) :
    Tendsto
      (fun omega =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) ^ (3 : ℕ) *
          d4ThetaHawkingSelfDualSeededSexticCompletion amplitude
            (xiSpectralPoint q) twoGreenNumerator oneGreenNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
      (𝓝 (d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient amplitude
        (xiSpectralPoint q))) := by
  have hbase :=
    d4ThetaHawkingSexticRepeatedMemoryCompletion_tendsto_triplePoleCoefficient
      amplitude q twoGreenNumerator oneGreenNumerator hN2 hN1
  have hconst : Tendsto
      (fun _ : ℂ =>
        d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient
          (xiSpectralPoint q))
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
      (𝓝 (d4ThetaHawkingAntiSelfDualUnitQuadraticCarrierCoefficient
        (xiSpectralPoint q))) := tendsto_const_nhds
  have hscaled := hconst.mul hbase
  convert hscaled using 1
  · funext omega
    simp only [d4ThetaHawkingSelfDualSeededSexticCompletion]
    ring
  · simp [d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient]

theorem d4ThetaHawkingSelfDualSeededSexticCompletion_cannot_cancel
    (amplitude : ℂ) (q : XiZeroCopy)
    (twoGreenNumerator oneGreenNumerator : ℂ → ℂ)
    (ha : amplitude ≠ 0)
    (hN2 : ContinuousAt twoGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
    (hN1 : ContinuousAt oneGreenNumerator
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)))) :
    ¬ Tendsto
      (fun omega =>
        (omega - thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))) ^ (3 : ℕ) *
          d4ThetaHawkingSelfDualSeededSexticCompletion amplitude
            (xiSpectralPoint q) twoGreenNumerator oneGreenNumerator omega)
      (𝓝[≠] (thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))))
      (𝓝 0) := by
  intro hzero
  have hcoefficient :=
    d4ThetaHawkingSelfDualSeededSexticCompletion_tendsto_triplePoleCoefficient
      amplitude q twoGreenNumerator oneGreenNumerator hN2 hN1
  have heq :
      d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient amplitude
        (xiSpectralPoint q) = 0 :=
    tendsto_nhds_unique hcoefficient hzero
  exact
    (d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient_xi_ne_zero_iff
      amplitude q).2 ha heq

theorem d4ThetaHawkingSelfDualSeededSexticPoleIncidence_iff
    (amplitude : ℂ) (ha : amplitude ≠ 0) (q : XiZeroCopy) :
    (d4ThetaHawkingChargeDecayInputFrequency 0 (xiSpectralPoint q) =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q)) ∧
      d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient amplitude
        (xiSpectralPoint q) ≠ 0) ↔
      (xiSpectralPoint q).im = 0 := by
  rw [and_iff_left
    ((d4ThetaHawkingSelfDualSeededSexticTriplePoleCoefficient_xi_ne_zero_iff
      amplitude q).2 ha)]
  exact d4ThetaHawkingSexticInputFrequency_eq_thirdQNMMinus_iff
    (xiSpectralPoint q)

end

end RHTower

