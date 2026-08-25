import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingQuadraticDealiasedJostPolarization

/-!
# Hawking--Teukolsky charge-decay resonance ladder

Time translation adds QNM frequencies. Reality supplies the partner frequency
`omega ↦ -star omega`. A negative dealiased return has phase charge `-2`, so a
degree-`8k+6` monomial contains `4k+2` direct modes and `4k+4` partners. Exact
Birmingham--Mokhtari decay then selects overtone `5k+3` and leaves detuning
`4(k+1)i Im(z)`. Hence every rung reaches an actual gravitational Jost zero
exactly at zero centered Xi tilt.

This is source-frequency incidence. Nonvanishing of its radial/helicity source
projection remains a separate Einstein--Teukolsky calculation.
-/

namespace RHTower

noncomputable section

/-- Number of direct fundamental QNMs in the charge-minus-two rung. -/
def d4ThetaHawkingChargeDecayDirectMultiplicity (k : ℕ) : ℕ := 4 * k + 2

/-- Number of real-field partners in the charge-minus-two rung. -/
def d4ThetaHawkingChargeDecayPartnerMultiplicity (k : ℕ) : ℕ := 4 * k + 4

/-- Negative-branch overtone selected by the charge-decay rung. -/
def d4ThetaHawkingChargeDecayTargetOvertone (k : ℕ) : ℕ := 5 * k + 3

lemma d4ThetaHawkingChargeDecay_degree (k : ℕ) :
    d4ThetaHawkingChargeDecayDirectMultiplicity k +
        d4ThetaHawkingChargeDecayPartnerMultiplicity k = 8 * k + 6 := by
  simp [d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayPartnerMultiplicity]
  omega

lemma d4ThetaHawkingChargeDecay_charge (k : ℕ) :
    d4ThetaHawkingChargeDecayDirectMultiplicity k + 2 =
      d4ThetaHawkingChargeDecayPartnerMultiplicity k := by
  simp [d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayPartnerMultiplicity]

lemma d4ThetaHawkingChargeDecayTargetOvertone_succ (k : ℕ) :
    d4ThetaHawkingChargeDecayTargetOvertone (k + 1) =
      d4ThetaHawkingChargeDecayTargetOvertone k + 5 := by
  simp [d4ThetaHawkingChargeDecayTargetOvertone]
  omega

/-- Fourier frequency of the fundamental charge-minus-two rung. -/
def d4ThetaHawkingChargeDecayInputFrequency (k : ℕ) (z : ℂ) : ℂ :=
  d4SingleSectorMonomialFrequency
    (d4ThetaHawkingChargeDecayDirectMultiplicity k)
    (d4ThetaHawkingChargeDecayPartnerMultiplicity k)
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 z)

/-- Exact frequency detuning along the Hawking charge-decay ladder. -/
theorem d4ThetaHawkingChargeDecayInputFrequency_sub_qnmMinus (k : ℕ) (z : ℂ) :
    d4ThetaHawkingChargeDecayInputFrequency k z -
        thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
      (4 * (k + 1) : ℂ) * Complex.I * (z.im : ℂ) := by
  simp [d4ThetaHawkingChargeDecayInputFrequency,
    d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayPartnerMultiplicity,
    d4ThetaHawkingChargeDecayTargetOvertone,
    d4SingleSectorMonomialFrequency, d4QNMRealFieldPartnerFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4ThetaCuspHawkingQuadraticDealiasedLift]
  apply Complex.ext <;> simp <;> ring

/-- A charge-decay rung is resonant exactly on the real centered spectral axis. -/
theorem d4ThetaHawkingChargeDecayInputFrequency_eq_qnmMinus_iff (k : ℕ) (z : ℂ) :
    d4ThetaHawkingChargeDecayInputFrequency k z =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) ↔
      z.im = 0 := by
  rw [← sub_eq_zero,
    d4ThetaHawkingChargeDecayInputFrequency_sub_qnmMinus]
  constructor
  · intro h
    have hk : (k : ℂ) + 1 ≠ 0 := by
      have hk' : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      simpa using hk'
    have hc : (4 * (k + 1) : ℂ) * Complex.I ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) hk) (by norm_num)
    have hz : (z.im : ℂ) = 0 := (mul_eq_zero.mp h).resolve_left hc
    exact_mod_cast hz
  · intro h
    simp [h]

/-- First rung is sextic and misses its third-overtone target by exactly `4 i Im(z)`. -/
theorem d4ThetaHawkingSexticInputFrequency_sub_thirdQNMMinus (z : ℂ) :
    d4ThetaHawkingChargeDecayInputFrequency 0 z -
        thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
      4 * Complex.I * (z.im : ℂ) := by
  simpa [d4ThetaHawkingChargeDecayTargetOvertone] using
    d4ThetaHawkingChargeDecayInputFrequency_sub_qnmMinus 0 z

/-- Sextic charge-minus-two incidence occurs exactly at zero Xi tilt. -/
theorem d4ThetaHawkingSexticInputFrequency_eq_thirdQNMMinus_iff (z : ℂ) :
    d4ThetaHawkingChargeDecayInputFrequency 0 z =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) ↔
      z.im = 0 := by
  simpa [d4ThetaHawkingChargeDecayTargetOvertone] using
    d4ThetaHawkingChargeDecayInputFrequency_eq_qnmMinus_iff 0 z

/-- Every target of the charge-decay ladder is an actual gravitational Jost zero. -/
theorem d4ThetaHawkingChargeDecay_boundaryJost_qnmMinus_eq_zero (k : ℕ) (z : ℂ) :
    d4GravitationalHypergeometricBoundaryJost
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z))
        (d4ThetaCuspHawkingQuadraticDealiasedLift z) = 0 := by
  unfold d4GravitationalHypergeometricBoundaryJost
    thetaCuspHawkingHypergeometricPhysicalBoundaryJost
    thetaCuspHawkingHypergeometricJost
  rw [thetaCuspHawkingHypergeometricJostMinus_qnm_zero]
  ring

/-- Simultaneous resonance of the complete charge-decay ladder over every Xi divisor. -/
def D4ThetaHawkingChargeDecayLadderResonates : Prop :=
  ∀ q : XiZeroCopy, ∀ k : ℕ,
    d4ThetaHawkingChargeDecayInputFrequency k (xiSpectralPoint q) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus
        (d4ThetaHawkingChargeDecayTargetOvertone k)
        (d4ThetaCuspHawkingQuadraticDealiasedLift (xiSpectralPoint q))

/-- Complete Hawking charge-decay resonance is equivalent to RH. -/
theorem riemannHypothesis_iff_d4ThetaHawkingChargeDecayLadderResonates :
    RiemannHypothesis ↔ D4ThetaHawkingChargeDecayLadderResonates := by
  rw [riemannHypothesis_iff_d4ThetaTeukolskyThermallyDealiasedSpectrumIsReal]
  constructor
  · intro h q k
    exact (d4ThetaHawkingChargeDecayInputFrequency_eq_qnmMinus_iff k
      (xiSpectralPoint q)).2
        ((d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).1
          (h q))
  · intro h q
    exact (d4ThetaTeukolskyThermallyDealiasedAngularEigenvalue_xi_im_eq_zero_iff q).2
      ((d4ThetaHawkingChargeDecayInputFrequency_eq_qnmMinus_iff 0
        (xiSpectralPoint q)).1 (h q 0))

end

end RHTower
