import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhaseSensitiveChiralWardAmplitude
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCubicPhaseCovarianceOpticalNoGo

/-!
# AIME/Ward seed-phase parity separation

The actual fundamental AIME numerator is cubic and odd under a seed half-turn.  The actual BM
mixed-horizon Ward amplitude has a quadratic Einstein carrier and is even.  Sampling their fixed
additive coupling at `A` and `-A` therefore gives exact two-phase tomography: the half-sum is the
HB/Deninger/FZZ/PW/RBH Ward channel, while the half-difference is the AIME channel.

The odd AIME sample is nonzero for every nonzero seed at every Xi descendant.  Hence no fixed
additive quadratic Ward counterterm can cancel AIME at both phases.  More sharply, if cancellation
occurs at one phase, the opposite phase equals minus twice the nonzero AIME numerator.  Viable
same-pole cancellation dynamics must contain a genuinely cubic `++-` contribution.

The even tomographic channel remains a faithful signed Ward receiver: after calibration it is the
Deninger charge, and its universal vanishing is RH-strength.

`[NEW] [SOURCE NO-GO] [PHASE TOMOGRAPHY] [EXACT SEPARATION] [LEAN-PROVED]`
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Actual quadratic BM mixed-horizon projection is even under a seed half-turn. -/
theorem d4BMMixedHorizonOpticalSourceProjection_neg_amplitude
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4BMMixedHorizonOpticalSourceProjection (-amplitude) orthogonalMixing q =
      d4BMMixedHorizonOpticalSourceProjection amplitude orthogonalMixing q := by
  rw [d4BMMixedHorizonOpticalSourceProjection_eq,
    d4BMMixedHorizonOpticalSourceProjection_eq]
  simp [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient]

/-- Fixed additive coupling of cubic AIME return and quadratic phase-sensitive BM Ward return. -/
def d4AIMEWardPhaseCoupledReturn
    (normalization amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) +
    normalization * d4BMMixedHorizonOpticalSourceProjection amplitude 0 q

/-- Half-turn sum extracts exactly the even quadratic Ward channel. -/
theorem d4AIMEWardPhaseCoupledReturn_halfTurn_sum
    (normalization amplitude : ℂ) (q : XiZeroCopy) :
    (d4AIMEWardPhaseCoupledReturn normalization amplitude q +
        d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q) / 2 =
      normalization * d4BMMixedHorizonOpticalSourceProjection amplitude 0 q := by
  rw [d4AIMEWardPhaseCoupledReturn, d4AIMEWardPhaseCoupledReturn,
    d4FundamentalQNMCrossBranchAIMENumerator_neg,
    d4BMMixedHorizonOpticalSourceProjection_neg_amplitude]
  ring

/-- Half-turn difference extracts exactly the odd cubic AIME channel. -/
theorem d4AIMEWardPhaseCoupledReturn_halfTurn_sub
    (normalization amplitude : ℂ) (q : XiZeroCopy) :
    (d4AIMEWardPhaseCoupledReturn normalization amplitude q -
        d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q) / 2 =
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) := by
  rw [d4AIMEWardPhaseCoupledReturn, d4AIMEWardPhaseCoupledReturn,
    d4FundamentalQNMCrossBranchAIMENumerator_neg,
    d4BMMixedHorizonOpticalSourceProjection_neg_amplitude]
  ring

/-- No fixed quadratic Ward counterterm cancels nonzero AIME at both seed phases. -/
theorem not_d4AIMEWardPhaseCoupledReturn_both_halfTurn_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (normalization : ℂ) (q : XiZeroCopy) :
    ¬ (d4AIMEWardPhaseCoupledReturn normalization amplitude q = 0 ∧
      d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q = 0) := by
  rintro ⟨hplus, hminus⟩
  have hnum :
      d4FundamentalQNMCrossBranchAIMENumerator amplitude (xiSpectralPoint q) = 0 := by
    rw [← d4AIMEWardPhaseCoupledReturn_halfTurn_sub normalization amplitude q,
      hplus, hminus]
    norm_num
  exact ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha) hnum

/-- Exact opposite-phase residue when one phase is tuned to cancel. -/
theorem d4AIMEWardPhaseCoupledReturn_neg_amplitude_of_eq_zero
    (amplitude normalization : ℂ) (q : XiZeroCopy)
    (hcancel : d4AIMEWardPhaseCoupledReturn normalization amplitude q = 0) :
    d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q =
      -2 * d4FundamentalQNMCrossBranchAIMENumerator amplitude
        (xiSpectralPoint q) := by
  have hsub := d4AIMEWardPhaseCoupledReturn_halfTurn_sub normalization amplitude q
  rw [hcancel] at hsub
  calc
    d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q =
        -2 * ((0 - d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q) / 2) := by
          ring
    _ = -2 * d4FundamentalQNMCrossBranchAIMENumerator amplitude
          (xiSpectralPoint q) := by rw [hsub]

/-- One-phase cancellation forces a nonzero doubled AIME residual at the opposite phase. -/
theorem d4AIMEWardPhaseCoupledReturn_neg_amplitude_ne_zero_of_eq_zero
    {amplitude : ℂ} (ha : amplitude ≠ 0) (normalization : ℂ) (q : XiZeroCopy)
    (hcancel : d4AIMEWardPhaseCoupledReturn normalization amplitude q = 0) :
    d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q ≠ 0 := by
  rw [d4AIMEWardPhaseCoupledReturn_neg_amplitude_of_eq_zero
    amplitude normalization q hcancel]
  exact mul_ne_zero (by norm_num)
    ((d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff amplitude q).mpr ha)

/-- Calibrated even tomographic sample is exactly the common signed Deninger charge. -/
theorem d4AIMEWardPhaseCoupledReturn_calibrated_halfTurn_sum_eq_deningerCharge
    {amplitude normalization : ℂ}
    (ha : amplitude ≠ 0) (hn : normalization ≠ 0) (q : XiZeroCopy) :
    ((d4AIMEWardPhaseCoupledReturn normalization amplitude q +
        d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q) / 2) /
        (normalization * hbXiPhaseSensitiveChiralWardMultiplier amplitude q) =
      fzzCigarParityDeningerReflectGaugeWardCharge q := by
  rw [d4AIMEWardPhaseCoupledReturn_halfTurn_sum,
    d4BMMixedHorizonOpticalSourceProjection_eq_chiralMultiplier_mul_deningerCharge]
  field_simp [hn, hbXiPhaseSensitiveChiralWardMultiplier_ne_zero ha q]

/-- Nondegenerate even tomographic channel vanishes exactly on the critical line. -/
theorem d4AIMEWardPhaseCoupledReturn_halfTurn_sum_eq_zero_iff_re_eq_half
    {amplitude normalization : ℂ}
    (ha : amplitude ≠ 0) (hn : normalization ≠ 0) (q : XiZeroCopy) :
    (d4AIMEWardPhaseCoupledReturn normalization amplitude q +
        d4AIMEWardPhaseCoupledReturn normalization (-amplitude) q) / 2 = 0 ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  rw [d4AIMEWardPhaseCoupledReturn_halfTurn_sum, mul_eq_zero]
  simp only [hn, false_or]
  exact d4BMMixedHorizonOpticalSourceProjection_eq_zero_iff_re_eq_half ha 0 q

/-- Universal vanishing of the canonical even two-phase sample. -/
def HBXiAIMEWardEvenPhaseCancellation : Prop :=
  ∀ q : XiZeroCopy,
    (d4AIMEWardPhaseCoupledReturn 1 1 q +
      d4AIMEWardPhaseCoupledReturn 1 (-1) q) / 2 = 0

/-- Canonical even phase cancellation is exactly RH; the odd AIME channel remains nonzero. -/
theorem hbXiAIMEWardEvenPhaseCancellation_iff_riemannHypothesis :
    HBXiAIMEWardEvenPhaseCancellation ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply (hbXiPhaseSensitiveChiralWardAmplitudeCancellation_iff_riemannHypothesis).mp
    intro q
    have hq := h q
    rw [d4AIMEWardPhaseCoupledReturn_halfTurn_sum] at hq
    simpa using hq
  · intro hRH q
    rw [d4AIMEWardPhaseCoupledReturn_halfTurn_sum]
    simpa using
      (hbXiPhaseSensitiveChiralWardAmplitudeCancellation_iff_riemannHypothesis.mpr hRH q)

theorem riemannHypothesis_iff_hbXiAIMEWardEvenPhaseCancellation :
    RiemannHypothesis ↔ HBXiAIMEWardEvenPhaseCancellation :=
  hbXiAIMEWardEvenPhaseCancellation_iff_riemannHypothesis.symm

end

end RHTower
