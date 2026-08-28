import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude

/-!
# Phase-sensitive reflected-pair coherent-cancellation no-go

The actual nonlinear BM mixed-horizon source is phase-sensitive and copywise darkness is exactly
critical-line placement. This module proves that a reflected-pair or global Ward cancellation is
strictly weaker.

The calibrated chiral coordinate is exactly odd under functional-equation reflection. Raw physical
amplitudes include copy-dependent, nowhere-zero multipliers. Every coherent two-channel return
factors as a relative-weight defect times the signed Ward charge. Off line, cancellation is
therefore equivalent only to matching the two weighted multipliers. Cross-weighting by the
opposite physical multiplier gives explicit nonzero weights that cancel two individually bright
off-critical channels.

Thus reflected-pair/global phase-sensitive Ward conservation cannot supply the missing RH
producer. A viable HB/FZZ-P/PW-B/RBH route must enforce copywise darkness or derive fixed,
source-native channel weights that exclude this cancellation freedom.

`[NEW] [PHASE-SENSITIVE] [BRIGHT-PAIR CANCELLATION] [GLOBAL-WARD NO-GO]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- The signed Ward coordinate is exactly odd under functional-equation reflection. -/
theorem fzzCigarParityDeningerReflectGaugeWardCharge_reflect
    (q : XiZeroCopy) :
    fzzCigarParityDeningerReflectGaugeWardCharge (xiZeroCopyReflectEquiv q) =
      -fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [fzzCigarParityDeningerReflectGaugeWardCharge_eq,
    fzzCigarParityDeningerReflectGaugeWardCharge_eq]
  simp only [deningerDivisorThetaEigen, xiZeroCopyReflect_re_eq_one_sub]
  push_cast
  ring

/-- The calibrated physical chiral amplitude is exactly reflection-odd. -/
theorem hbXiCalibratedPhaseSensitiveChiralWardAmplitude_reflect
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiCalibratedPhaseSensitiveChiralWardAmplitude amplitude orthogonalMixing
        (xiZeroCopyReflectEquiv q) =
      -hbXiCalibratedPhaseSensitiveChiralWardAmplitude amplitude orthogonalMixing q := by
  rw [hbXiCalibratedPhaseSensitiveChiralWardAmplitude_eq_deningerCharge ha,
    hbXiCalibratedPhaseSensitiveChiralWardAmplitude_eq_deningerCharge ha,
    fzzCigarParityDeningerReflectGaugeWardCharge_reflect]

/-- Coherent physical return from one Xi copy and its reflected partner. -/
def hbXiPhaseSensitiveReflectedPairCoherentReturn
    (leftWeight rightWeight amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  leftWeight * d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q +
    rightWeight * d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing
      (xiZeroCopyReflectEquiv q)

/-- Exact factorization of every reflected-pair coherent return. -/
theorem hbXiPhaseSensitiveReflectedPairCoherentReturn_eq
    (leftWeight rightWeight amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveReflectedPairCoherentReturn
        leftWeight rightWeight amplitude orthogonalMixing q =
      (leftWeight * hbXiPhaseSensitiveChiralWardMultiplier amplitude q -
        rightWeight * hbXiPhaseSensitiveChiralWardMultiplier amplitude
          (xiZeroCopyReflectEquiv q)) *
        fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [hbXiPhaseSensitiveReflectedPairCoherentReturn,
    d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge,
    fzzCigarParityDeningerReflectGaugeWardCharge_reflect]
  ring

/-- Off the critical line, coherent cancellation constrains only relative channel weights. -/
theorem hbXiPhaseSensitiveReflectedPairCoherentReturn_eq_zero_iff_weights
    (leftWeight rightWeight amplitude orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveReflectedPairCoherentReturn
        leftWeight rightWeight amplitude orthogonalMixing q = 0 ↔
      leftWeight * hbXiPhaseSensitiveChiralWardMultiplier amplitude q =
        rightWeight * hbXiPhaseSensitiveChiralWardMultiplier amplitude
          (xiZeroCopyReflectEquiv q) := by
  rw [hbXiPhaseSensitiveReflectedPairCoherentReturn_eq, mul_eq_zero, sub_eq_zero]
  have hcharge : fzzCigarParityDeningerReflectGaugeWardCharge q ≠ 0 :=
    (fzzCigarParityDeningerReflectGaugeWardCharge_eq_zero_iff q).not.mpr (by
      simpa only [deningerDivisorThetaEigen] using hoff)
  simp only [hcharge, or_false]

/-- Cross-weighting by the two physical multipliers cancels every reflected pair exactly. -/
theorem hbXiPhaseSensitiveReflectedPairCoherentReturn_crossWeights_eq_zero
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveReflectedPairCoherentReturn
        (hbXiPhaseSensitiveChiralWardMultiplier amplitude (xiZeroCopyReflectEquiv q))
        (hbXiPhaseSensitiveChiralWardMultiplier amplitude q)
        amplitude orthogonalMixing q = 0 := by
  rw [hbXiPhaseSensitiveReflectedPairCoherentReturn_eq]
  ring

/-- Off line, cross-weight cancellation combines two nonzero weights and two individually bright
raw phase-sensitive channels. -/
theorem exists_nonzero_crossWeights_cancel_two_bright_reflected_channels
    {amplitude : ℂ} (ha : amplitude ≠ 0) (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ leftWeight rightWeight : ℂ,
      leftWeight ≠ 0 ∧ rightWeight ≠ 0 ∧
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q ≠ 0 ∧
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing
        (xiZeroCopyReflectEquiv q) ≠ 0 ∧
      hbXiPhaseSensitiveReflectedPairCoherentReturn
        leftWeight rightWeight amplitude orthogonalMixing q = 0 := by
  have hoffR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    intro h
    apply hoff
    linarith
  refine ⟨hbXiPhaseSensitiveChiralWardMultiplier amplitude (xiZeroCopyReflectEquiv q),
    hbXiPhaseSensitiveChiralWardMultiplier amplitude q,
    hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha (xiZeroCopyReflectEquiv q),
    hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha q, ?_, ?_,
    hbXiPhaseSensitiveReflectedPairCoherentReturn_crossWeights_eq_zero
      amplitude orthogonalMixing q⟩
  · exact (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      ha orthogonalMixing q).not.mpr (by
        simpa only [deningerDivisorThetaEigen] using hoff)
  · exact (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      ha orthogonalMixing (xiZeroCopyReflectEquiv q)).not.mpr (by
        simpa only [deningerDivisorThetaEigen] using hoffR)

/-- Closed no-go: every off-line copy admits nonzero coherent weights cancelling two individually
bright physical Ward channels. -/
def HBXiPhaseSensitiveReflectedPairBrightCancellation : Prop :=
  ∀ q : XiZeroCopy,
    (q.1 : ℂ).re ≠ 1 / 2 →
      ∃ leftWeight rightWeight : ℂ,
        leftWeight ≠ 0 ∧ rightWeight ≠ 0 ∧
        d4BMMixedHorizonOpticalSourceProjection 1 0 q ≠ 0 ∧
        d4BMMixedHorizonOpticalSourceProjection 1 0
          (xiZeroCopyReflectEquiv q) ≠ 0 ∧
        hbXiPhaseSensitiveReflectedPairCoherentReturn
          leftWeight rightWeight 1 0 q = 0

/-- **[PHASE-SENSITIVE GLOBAL-WARD NO-GO]** Reflected-pair coherent cancellation is universal,
including at every pair of bright off-critical channels, and therefore cannot imply RH. -/
theorem hbXiPhaseSensitiveReflectedPairBrightCancellation :
    HBXiPhaseSensitiveReflectedPairBrightCancellation := by
  intro q hoff
  exact exists_nonzero_crossWeights_cancel_two_bright_reflected_channels
    (by norm_num) 0 q hoff

end

end RHTower
