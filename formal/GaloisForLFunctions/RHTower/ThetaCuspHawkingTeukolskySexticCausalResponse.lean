import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskySexticJostDealiasing
import GaloisForLFunctions.RHTower.ThetaCuspHawkingAPSEtaBackreactionBoundary

/-!
# Sextic Hawking--Teukolsky causal response

The retarded zero-data response of one damped QNM pole to one nonlinear source carrier is an
exponential divided difference.  Birmingham--Mokhtari charge-decay detuning is purely imaginary,
so the response factors into the target QNM time character and a real causal factor.  At the
first, sextic rung this factor becomes the secular term `t` exactly on the centered Xi axis.

The real detuning rate is also the exact horizon mass-jet asymmetry, but ordinary decay does not
control its sign: every sextic source carrier decays throughout the Xi strip.  The stronger
QNM-normalized no-amplification law selects one half-strip; imposing it on the functional-equation
reflected retarded sector as well is equivalent to the sextic Jost zero.  Deriving that normalized
law from the nonlinear Einstein--Teukolsky horizon-energy identity remains the physical producer.

**[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]** Exact causal factorization, secular
classification, absolute-decay no-go, and reflected normalized-gain/Jost classification.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

def d4ThetaHawkingCausalDividedDifference (delta t : ℝ) : ℝ :=
  if delta = 0 then t else (Real.exp (delta * t) - 1) / delta

def d4ThetaHawkingCausalModeResponse (sourceFrequency poleFrequency t : ℂ) : ℂ :=
  if sourceFrequency = poleFrequency then
    t * Complex.exp (-Complex.I * poleFrequency * t)
  else
    (Complex.exp (-Complex.I * sourceFrequency * t) -
      Complex.exp (-Complex.I * poleFrequency * t)) /
        (Complex.I * (poleFrequency - sourceFrequency))

/-- A pure imaginary frequency detuning becomes a real exponential divided difference. -/
theorem d4ThetaHawkingCausalModeResponse_pureImaginaryDetuning
    (poleFrequency : ℂ) (delta t : ℝ) :
    d4ThetaHawkingCausalModeResponse
        (poleFrequency + Complex.I * (delta : ℂ)) poleFrequency (t : ℂ) =
      Complex.exp (-Complex.I * poleFrequency * t) *
        (d4ThetaHawkingCausalDividedDifference delta t : ℂ) := by
  by_cases hdelta : delta = 0
  · subst delta
    simp [d4ThetaHawkingCausalModeResponse,
      d4ThetaHawkingCausalDividedDifference]
    ring_nf
  · have hfreq : poleFrequency + Complex.I * (delta : ℂ) ≠ poleFrequency := by
      intro h
      have hzero : Complex.I * (delta : ℂ) = 0 := by linear_combination h
      exact hdelta (by exact_mod_cast (mul_eq_zero.mp hzero).resolve_left Complex.I_ne_zero)
    rw [d4ThetaHawkingCausalModeResponse, if_neg hfreq,
      d4ThetaHawkingCausalDividedDifference, if_neg hdelta]
    have hexp :
        Complex.exp (-Complex.I * (poleFrequency + Complex.I * (delta : ℂ)) * t) =
          Complex.exp (-Complex.I * poleFrequency * t) *
            (Real.exp (delta * t) : ℂ) := by
      rw [show -Complex.I * (poleFrequency + Complex.I * (delta : ℂ)) * t =
          -Complex.I * poleFrequency * t + ((delta * t : ℝ) : ℂ) by
        push_cast
        ring_nf
        rw [Complex.I_sq]
        ring]
      rw [Complex.exp_add]
      simp
    rw [hexp]
    have hdeltaC : (delta : ℂ) ≠ 0 := by exact_mod_cast hdelta
    rw [show Complex.I *
        (poleFrequency - (poleFrequency + Complex.I * (delta : ℂ))) =
          (delta : ℂ) by
      ring_nf
      rw [Complex.I_sq]
      ring]
    push_cast
    field_simp [hdeltaC]

@[simp]
theorem d4ThetaHawkingCausalModeResponse_zero (sourceFrequency poleFrequency : ℂ) :
    d4ThetaHawkingCausalModeResponse sourceFrequency poleFrequency 0 = 0 := by
  by_cases h : sourceFrequency = poleFrequency <;>
    simp [d4ThetaHawkingCausalModeResponse, h]

/-- Causal response slope is the source-to-pole translation-character ratio. -/
theorem hasDerivAt_d4ThetaHawkingCausalDividedDifference
    (delta t : ℝ) :
    HasDerivAt (d4ThetaHawkingCausalDividedDifference delta)
      (Real.exp (delta * t)) t := by
  by_cases hdelta : delta = 0
  · subst delta
    rw [show d4ThetaHawkingCausalDividedDifference 0 = id by
      funext x
      simp [d4ThetaHawkingCausalDividedDifference]]
    simpa using hasDerivAt_id t
  · change HasDerivAt
      (fun x : ℝ => if delta = 0 then x else (Real.exp (delta * x) - 1) / delta)
      (Real.exp (delta * t)) t
    simp only [hdelta, if_false]
    have hlin : HasDerivAt (fun x : ℝ => delta * x) delta t :=
      hasDerivAt_const_mul delta
    have h : HasDerivAt
        (fun x : ℝ => (Real.exp (delta * x) - 1) / delta)
        ((Real.exp (delta * t) * delta) / delta) t :=
      (hlin.exp.sub_const 1).div_const delta
    convert h using 1
    field_simp [hdelta]

def d4ThetaHawkingChargeDecayDetuningRate (k : ℕ) (z : ℂ) : ℝ :=
  4 * ((k + 1 : ℕ) : ℝ) * z.im

theorem d4ThetaHawkingChargeDecayInputFrequency_eq_pole_add_detuning
    (k : ℕ) (z : ℂ) :
    d4ThetaHawkingChargeDecayInputFrequency k z =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) +
        Complex.I * (d4ThetaHawkingChargeDecayDetuningRate k z : ℂ) := by
  apply sub_eq_zero.mp
  calc
    d4ThetaHawkingChargeDecayInputFrequency k z -
        (thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) +
            Complex.I * (d4ThetaHawkingChargeDecayDetuningRate k z : ℂ)) =
      (d4ThetaHawkingChargeDecayInputFrequency k z -
        thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z)) -
        Complex.I * (d4ThetaHawkingChargeDecayDetuningRate k z : ℂ) := by ring
    _ = 0 := by
      rw [d4ThetaHawkingChargeDecayInputFrequency_sub_qnmMinus]
      simp [d4ThetaHawkingChargeDecayDetuningRate]
      ring

theorem d4ThetaHawkingChargeDecayInputFrequency_im_eq
    (k : ℕ) (q : XiZeroCopy) :
    (d4ThetaHawkingChargeDecayInputFrequency k (xiSpectralPoint q)).im =
      ((8 * k + 6 : ℕ) : ℝ) * (-1 - (q.1 : ℂ).re / 2) := by
  rw [show
    (d4ThetaHawkingChargeDecayInputFrequency k (xiSpectralPoint q)).im =
      (((d4ThetaHawkingChargeDecayDirectMultiplicity k : ℕ) : ℝ) +
        ((d4ThetaHawkingChargeDecayPartnerMultiplicity k : ℕ) : ℝ)) *
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus 0
            (xiSpectralPoint q)).im by
    simp [d4ThetaHawkingChargeDecayInputFrequency,
      d4SingleSectorMonomialFrequency, d4QNMRealFieldPartnerFrequency]
    ring]
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus_im]
  simp [d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayPartnerMultiplicity,
    xiSpectralPoint, thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  ring

theorem d4ThetaHawkingChargeDecayInputFrequency_im_lt_zero
    (k : ℕ) (q : XiZeroCopy) :
    (d4ThetaHawkingChargeDecayInputFrequency k (xiSpectralPoint q)).im < 0 := by
  rw [d4ThetaHawkingChargeDecayInputFrequency_im_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hdegree : (0 : ℝ) < ((8 * k + 6 : ℕ) : ℝ) := by positivity
  nlinarith

def d4ThetaHawkingChargeDecayCausalResponse (k : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  d4ThetaHawkingCausalModeResponse
    (d4ThetaHawkingChargeDecayInputFrequency k z)
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus
      (d4ThetaHawkingChargeDecayTargetOvertone k)
      (d4ThetaCuspHawkingQuadraticDealiasedLift z)) (t : ℂ)

theorem d4ThetaHawkingChargeDecayCausalResponse_factorization
    (k : ℕ) (z : ℂ) (t : ℝ) :
    d4ThetaHawkingChargeDecayCausalResponse k z t =
      Complex.exp (-Complex.I *
        thetaCuspHawkingTopologicalBlackHoleQNMMinus
          (d4ThetaHawkingChargeDecayTargetOvertone k)
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) * t) *
        (d4ThetaHawkingCausalDividedDifference
          (d4ThetaHawkingChargeDecayDetuningRate k z) t : ℂ) := by
  unfold d4ThetaHawkingChargeDecayCausalResponse
  rw [d4ThetaHawkingChargeDecayInputFrequency_eq_pole_add_detuning]
  exact d4ThetaHawkingCausalModeResponse_pureImaginaryDetuning _ _ _

theorem d4ThetaHawkingSexticCausalResponse_eq_secular_of_im_eq_zero
    (z : ℂ) (hz : z.im = 0) (t : ℝ) :
    d4ThetaHawkingChargeDecayCausalResponse 0 z t =
      (t : ℂ) * Complex.exp (-Complex.I *
        thetaCuspHawkingTopologicalBlackHoleQNMMinus 3
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) * t) := by
  rw [d4ThetaHawkingChargeDecayCausalResponse_factorization]
  simp [d4ThetaHawkingChargeDecayDetuningRate, hz,
    d4ThetaHawkingCausalDividedDifference, d4ThetaHawkingChargeDecayTargetOvertone]
  ring_nf

theorem d4ThetaHawkingChargeDecayDetuningRate_reflect (k : ℕ) (q : XiZeroCopy) :
    d4ThetaHawkingChargeDecayDetuningRate k
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      -d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q) := by
  rw [xiSpectralPoint_reflect]
  simp [d4ThetaHawkingChargeDecayDetuningRate]

theorem d4ThetaHawkingChargeDecayDetuningRate_eq_apsEta
    (k : ℕ) (q : XiZeroCopy) :
    d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q) =
      2 * ((k + 1 : ℕ) : ℝ) * thermalCircleAPSEta (q.1 : ℂ).re := by
  unfold d4ThetaHawkingChargeDecayDetuningRate thermalCircleAPSEta
  rw [xiSpectralPoint_im_eq]
  ring

theorem d4ThetaHawkingChargeDecayDetuningRate_eq_horizonMassJetDefect
    (k n : ℕ) (q : XiZeroCopy) :
    d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q) =
      4 * ((k + 1 : ℕ) : ℝ) *
        d4BMXiReflectedHorizonMassJetDefect n q := by
  rw [d4ThetaHawkingChargeDecayDetuningRate_eq_apsEta,
    d4BMXiReflectedHorizonMassJetDefect_eq_half_eta]
  ring

def d4ThetaHawkingChargeDecayNormalizedCausalResponse
    (k : ℕ) (q : XiZeroCopy) (t : ℝ) : ℝ :=
  d4ThetaHawkingCausalDividedDifference
    (d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q)) t

theorem hasDerivAt_d4ThetaHawkingChargeDecayNormalizedCausalResponse
    (k : ℕ) (q : XiZeroCopy) (t : ℝ) :
    HasDerivAt (d4ThetaHawkingChargeDecayNormalizedCausalResponse k q)
      (Real.exp
        (d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q) * t)) t := by
  exact hasDerivAt_d4ThetaHawkingCausalDividedDifference _ _

def D4ThetaHawkingRetardedUnitGainNoAmplification (k : ℕ) (q : XiZeroCopy) : Prop :=
  Real.exp (d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q)) ≤ 1

/-- One-sided normalized no-amplification selects one closed half of the Xi strip. -/
theorem d4ThetaHawkingRetardedUnitGainNoAmplification_iff_re_ge_half
    (k : ℕ) (q : XiZeroCopy) :
    D4ThetaHawkingRetardedUnitGainNoAmplification k q ↔
      1 / 2 ≤ (q.1 : ℂ).re := by
  unfold D4ThetaHawkingRetardedUnitGainNoAmplification
    d4ThetaHawkingChargeDecayDetuningRate
  rw [Real.exp_le_one_iff, xiSpectralPoint_im_eq]
  have hk : 0 < 4 * ((k + 1 : ℕ) : ℝ) := by positivity
  constructor <;> intro h <;> nlinarith

theorem d4ThetaHawkingRetardedUnitGainNoAmplification_iff_horizonMassJet_nonpos
    (k n : ℕ) (q : XiZeroCopy) :
    D4ThetaHawkingRetardedUnitGainNoAmplification k q ↔
      d4BMXiReflectedHorizonMassJetDefect n q ≤ 0 := by
  unfold D4ThetaHawkingRetardedUnitGainNoAmplification
  rw [Real.exp_le_one_iff,
    d4ThetaHawkingChargeDecayDetuningRate_eq_horizonMassJetDefect]
  have hk : 0 < 4 * ((k + 1 : ℕ) : ℝ) := by positivity
  constructor <;> intro h <;> nlinarith

theorem d4ThetaHawkingRetardedMirrorPair_noAmplification_iff
    (k : ℕ) (q : XiZeroCopy) :
    (D4ThetaHawkingRetardedUnitGainNoAmplification k q ∧
      D4ThetaHawkingRetardedUnitGainNoAmplification k (xiZeroCopyReflectEquiv q)) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [show D4ThetaHawkingRetardedUnitGainNoAmplification k
      (xiZeroCopyReflectEquiv q) ↔
      Real.exp (-d4ThetaHawkingChargeDecayDetuningRate k (xiSpectralPoint q)) ≤ 1 by
    simp [D4ThetaHawkingRetardedUnitGainNoAmplification,
      d4ThetaHawkingChargeDecayDetuningRate_reflect]]
  unfold D4ThetaHawkingRetardedUnitGainNoAmplification
  rw [Real.exp_le_one_iff, Real.exp_le_one_iff]
  unfold d4ThetaHawkingChargeDecayDetuningRate
  rw [xiSpectralPoint_im_eq]
  constructor
  · rintro ⟨h, hn⟩
    have hkpos : 0 < 4 * ((k + 1 : ℕ) : ℝ) := by positivity
    have hz : (q.1 : ℂ).re - 1 / 2 = 0 := by nlinarith
    linarith
  · intro h
    constructor <;> simp [h]

theorem d4ThetaHawkingRetardedMirrorPair_noAmplification_iff_sexticJostZero
    (q : XiZeroCopy) :
    (D4ThetaHawkingRetardedUnitGainNoAmplification 0 q ∧
      D4ThetaHawkingRetardedUnitGainNoAmplification 0
        (xiZeroCopyReflectEquiv q)) ↔
      d4ThetaHawkingChargeDecayNegativeJost 0 (xiSpectralPoint q) = 0 := by
  exact (d4ThetaHawkingRetardedMirrorPair_noAmplification_iff 0 q).trans
    (d4ThetaHawkingSexticNegativeJost_xi_eq_zero_iff q).symm

end

end RHTower
