import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingQuadraticDealiasedJostPolarization

/-!
# Hawking--Teukolsky charge-decay resonance ladder

Time translation adds frequencies of radiative ancestors. Reality supplies the
partner frequency `omega ↦ -star omega`. For `r` direct fundamental modes and
`r+2` partners, exact Birmingham--Mokhtari decay gives detuning
`i ((r+2) Im(z) + (4n-5r-2)/2)` from negative overtone `n`. On the centered
axis, matching is therefore the Diophantine law `4n=5r+2`, whose complete
solution is `r=4k+2`, `n=5k+3`. The radiative degrees are exactly `8k+6`.

Stationary horizon memory carries zero frequency. It may raise perturbative
degree by neutral pairs, but it cannot change this radiative-ancestry law or
reduce the six-radiative-mode threshold.

This is source-frequency incidence, not a resonance-forcing principle: a
nonlinear Teukolsky source may respond at a combination frequency away from a
linear QNM pole. Nonvanishing and forced pole incidence are separate dynamical
questions.
-/

namespace RHTower

noncomputable section

/-- Frequency carried by `r` direct fundamental radiative ancestors and the
`r+2` real-field partners required for charge `-2`. -/
def d4ThetaHawkingChargeMinusTwoFundamentalFrequency (r : ℕ) (z : ℂ) : ℂ :=
  d4SingleSectorMonomialFrequency r (r + 2)
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0 z)

/-- Exact detuning of every charge-minus-two fundamental radiative monomial
from negative Birmingham--Mokhtari overtone `n`. -/
theorem d4ThetaHawkingChargeMinusTwoFundamentalFrequency_sub_qnmMinus
    (r n : ℕ) (z : ℂ) :
    d4ThetaHawkingChargeMinusTwoFundamentalFrequency r z -
        thetaCuspHawkingTopologicalBlackHoleQNMMinus n
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
      Complex.I *
        (((r + 2 : ℕ) : ℂ) * (z.im : ℂ) +
          (4 * (n : ℂ) - 5 * (r : ℂ) - 2) / 2) := by
  simp [d4ThetaHawkingChargeMinusTwoFundamentalFrequency,
    d4SingleSectorMonomialFrequency, d4QNMRealFieldPartnerFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4ThetaCuspHawkingQuadraticDealiasedLift]
  apply Complex.ext <;> simp <;> ring

private lemma d4ThetaHawkingCriticalChargeMinusTwoDetuning_zero_iff
    (r n : ℕ) :
    (Complex.I * ((4 * (n : ℂ) - 5 * (r : ℂ) - 2) / 2) = 0) ↔
      4 * n = 5 * r + 2 := by
  simp only [mul_eq_zero, Complex.I_ne_zero, false_or, div_eq_zero_iff,
    OfNat.ofNat_ne_zero, or_false]
  constructor
  · intro h
    have hc : (4 : ℂ) * n = 5 * r + 2 := by linear_combination h
    exact_mod_cast hc
  · intro h
    have hc : (4 : ℂ) * n = 5 * r + 2 := by exact_mod_cast h
    linear_combination hc

/-- On the centered axis, charge-minus-two matching is exactly one integral
decay-balance equation. -/
theorem d4ThetaHawkingChargeMinusTwoFundamentalFrequency_eq_qnmMinus_iff
    (r n : ℕ) (z : ℂ) (hz : z.im = 0) :
    d4ThetaHawkingChargeMinusTwoFundamentalFrequency r z =
        thetaCuspHawkingTopologicalBlackHoleQNMMinus n
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) ↔
      4 * n = 5 * r + 2 := by
  rw [← sub_eq_zero,
    d4ThetaHawkingChargeMinusTwoFundamentalFrequency_sub_qnmMinus]
  simp only [hz, Complex.ofReal_zero, mul_zero, zero_add]
  exact d4ThetaHawkingCriticalChargeMinusTwoDetuning_zero_iff r n

/-- Complete natural-number classification of centered charge-minus-two
fundamental returns. -/
theorem d4ThetaHawkingChargeMinusTwoCriticalMatch_classification (r n : ℕ) :
    4 * n = 5 * r + 2 ↔
      ∃ k : ℕ, r = 4 * k + 2 ∧ n = 5 * k + 3 := by
  constructor
  · intro h
    have hr : r % 4 = 2 := by omega
    refine ⟨r / 4, ?_, ?_⟩ <;> omega
  · rintro ⟨k, rfl, rfl⟩
    omega

/-- Every centered charge-minus-two return needs at least six radiative
ancestors, independently of any zero-frequency memory dressing. -/
theorem d4ThetaHawkingChargeMinusTwo_six_le_radiativeDegree_of_match
    (r n : ℕ) (h : 4 * n = 5 * r + 2) :
    6 ≤ r + (r + 2) := by
  obtain ⟨k, rfl, _⟩ :=
    (d4ThetaHawkingChargeMinusTwoCriticalMatch_classification r n).1 h
  omega

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
