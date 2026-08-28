import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveReflectedPairCancellationNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEPacketPeierlsClassification

/-!
# Radiation-dressed source-FE coherent-cancellation no-go

HC88 proves that suitable coherent weights cancel two bright reflected nonlinear Ward channels.
This module closes the strongest objection: those weights need not be external or arbitrary.
Literal BM source functional-equation transport, dressed by the actual nonzero retarded ingoing
Green coefficient, canonically constructs them.

The raw unit-seed mixed-horizon projection is exactly Green propagation of the literal polarized
source. Dressing the source FE cocycle by reflected/unreflected Green transfer yields an exact
anti-linear involution transporting the raw nonlinear Ward amplitude. Its canonical source-native
weights cancel every reflected pair. Off the critical line, both weights and both raw channels are
nonzero, and the weights satisfy the unique HC88 cancellation ratio.

Thus source nativeness and causal propagation do not rescue global/reflected-pair Ward
conservation. A viable HB/FZZ-P/PW-B/RBH producer must derive divisor-independent or
reflection-real weights, or enforce copywise darkness before FE aggregation.

`[NEW] [RADIATIVE FE COCYCLE] [SOURCE-NATIVE WEIGHTS] [BRIGHT CANCELLATION] [NO-GO]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- The actual raw unit-seed Ward channel is retarded Green propagation of the literal nonlinear
polarized source. -/
theorem d4BMMixedHorizonOpticalSourceProjection_one_eq_green_mul_literalSource
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing q =
      d4BMGaugeFixedSecondHarmonicGreen q *
        d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude]
  ring

/-- Literal-source anti-linear FE cocycle dressed by the actual retarded Green transfer. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFECocycle (q : XiZeroCopy) : ℂ :=
  d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
      hbXiPeierlsUnitSourceFECocycle q /
    (starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q)

/-- The radiative source-FE cocycle transports the actual raw nonlinear Ward channel exactly. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_transport
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q *
        (starRingEnd ℂ)
          (d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing q) =
      d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing
        (xiZeroCopyReflectEquiv q) := by
  rw [d4BMMixedHorizonOpticalSourceProjection_one_eq_green_mul_literalSource,
    d4BMMixedHorizonOpticalSourceProjection_one_eq_green_mul_literalSource,
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle, map_mul]
  have hG : (starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q)
  calc
    (d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
          hbXiPeierlsUnitSourceFECocycle q /
        (starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q)) *
          ((starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q) *
            (starRingEnd ℂ) (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) =
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
        (hbXiPeierlsUnitSourceFECocycle q *
          (starRingEnd ℂ) (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) := by
            field_simp [hG]
    _ = d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) *
        d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q) := by
            rw [hbXiPeierlsUnitSourceFECocycle_sourceTransport]

/-- Green dressing preserves the anti-linear FE involution. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle (xiZeroCopyReflectEquiv q) *
        (starRingEnd ℂ) (hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q) = 1 := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFECocycle,
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle,
    xiZeroCopyReflectEquiv_apply_apply, map_div₀, map_mul]
  have hGq := d4BMGaugeFixedSecondHarmonicGreen_ne_zero q
  have hGR := d4BMGaugeFixedSecondHarmonicGreen_ne_zero (xiZeroCopyReflectEquiv q)
  have hstarGq : (starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hGq
  have hstarGR :
      (starRingEnd ℂ)
          (d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hGR
  have hccGq :
      (starRingEnd ℂ) ((starRingEnd ℂ) (d4BMGaugeFixedSecondHarmonicGreen q)) =
        d4BMGaugeFixedSecondHarmonicGreen q := by simp
  rw [hccGq]
  calc
    (d4BMGaugeFixedSecondHarmonicGreen q *
          hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) /
        (starRingEnd ℂ)
          (d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q))) *
      (((starRingEnd ℂ)
          (d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q)) *
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q)) /
          d4BMGaugeFixedSecondHarmonicGreen q) =
        hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) := by
            field_simp [hGq, hstarGR]
    _ = 1 := hbXiPeierlsUnitSourceFECocycle_involutive q

/-- The radiative source-FE cocycle never vanishes. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_ne_zero
    (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q ≠ 0 := by
  intro hzero
  have hinv := hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_involutive q
  rw [hzero, map_zero, mul_zero] at hinv
  norm_num at hinv

/-- Canonical left coherent weight obtained from source-FE transport of one raw channel. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight
    (orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  -hbXiPhaseSensitiveUnitRadiativeSourceFECocycle q *
    (starRingEnd ℂ)
      (d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing q)

/-- Canonical right coherent weight is the original raw source channel. -/
def hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight
    (orthogonalMixing : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing q

/-- The source-FE left weight is exactly the negative reflected raw channel. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight_eq_neg_reflected
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight orthogonalMixing q =
      -d4BMMixedHorizonOpticalSourceProjection 1 orthogonalMixing
        (xiZeroCopyReflectEquiv q) := by
  rw [hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight, neg_mul,
    hbXiPhaseSensitiveUnitRadiativeSourceFECocycle_transport]

/-- Literal source FE plus retarded propagation canonically cancels the reflected raw pair. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEWeights_cancel
    (orthogonalMixing : ℂ) (q : XiZeroCopy) :
    hbXiPhaseSensitiveReflectedPairCoherentReturn
        (hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight orthogonalMixing q)
        (hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight orthogonalMixing q)
        1 orthogonalMixing q = 0 := by
  rw [hbXiPhaseSensitiveReflectedPairCoherentReturn,
    hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight_eq_neg_reflected,
    hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight]
  ring

/-- Off line, source-native radiative weights satisfy the unique HC88 cancellation equation. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEWeights_unique_ratio
    (orthogonalMixing : ℂ) (q : XiZeroCopy)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight orthogonalMixing q *
        hbXiPhaseSensitiveChiralWardMultiplier 1 q =
      hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight orthogonalMixing q *
        hbXiPhaseSensitiveChiralWardMultiplier 1 (xiZeroCopyReflectEquiv q) := by
  exact
    (hbXiPhaseSensitiveReflectedPairCoherentReturn_eq_zero_iff_weights
      (hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight orthogonalMixing q)
      (hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight orthogonalMixing q)
      1 orthogonalMixing q hoff).mp
        (hbXiPhaseSensitiveUnitRadiativeSourceFEWeights_cancel orthogonalMixing q)

/-- Closed source-native no-go statement. -/
def HBXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation : Prop :=
  ∀ q : XiZeroCopy,
    (q.1 : ℂ).re ≠ 1 / 2 →
      hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight 0 q ≠ 0 ∧
      hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight 0 q ≠ 0 ∧
      d4BMMixedHorizonOpticalSourceProjection 1 0 q ≠ 0 ∧
      d4BMMixedHorizonOpticalSourceProjection 1 0
        (xiZeroCopyReflectEquiv q) ≠ 0 ∧
      hbXiPhaseSensitiveReflectedPairCoherentReturn
        (hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight 0 q)
        (hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight 0 q) 1 0 q = 0 ∧
      hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight 0 q *
          hbXiPhaseSensitiveChiralWardMultiplier 1 q =
        hbXiPhaseSensitiveUnitRadiativeSourceFERightWeight 0 q *
          hbXiPhaseSensitiveChiralWardMultiplier 1 (xiZeroCopyReflectEquiv q)

/-- **[SOURCE-NATIVE WEIGHT NO-GO]** Literal source FE and retarded propagation themselves produce
the unique nonzero weights cancelling every bright reflected off-line Ward pair. -/
theorem hbXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation :
    HBXiPhaseSensitiveUnitRadiativeSourceFEBrightCancellation := by
  intro q hoff
  have hoffR : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≠ 1 / 2 := by
    rw [xiZeroCopyReflect_re_eq_one_sub]
    intro h
    apply hoff
    linarith
  have hP : d4BMMixedHorizonOpticalSourceProjection 1 0 q ≠ 0 :=
    (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      one_ne_zero 0 q).not.mpr (by
        simpa only [deningerDivisorThetaEigen] using hoff)
  have hPR : d4BMMixedHorizonOpticalSourceProjection 1 0
      (xiZeroCopyReflectEquiv q) ≠ 0 :=
    (d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half
      one_ne_zero 0 (xiZeroCopyReflectEquiv q)).not.mpr (by
        simpa only [deningerDivisorThetaEigen] using hoffR)
  refine ⟨?_, ?_, hP, hPR,
    hbXiPhaseSensitiveUnitRadiativeSourceFEWeights_cancel 0 q,
    hbXiPhaseSensitiveUnitRadiativeSourceFEWeights_unique_ratio 0 q hoff⟩
  · rw [hbXiPhaseSensitiveUnitRadiativeSourceFELeftWeight_eq_neg_reflected]
    exact neg_ne_zero.mpr hPR
  · exact hP

end

end RHTower
