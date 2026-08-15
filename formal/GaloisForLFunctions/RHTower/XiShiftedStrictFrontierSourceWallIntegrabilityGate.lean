import GaloisForLFunctions.RHTower.XiShiftedStrictFrontierChristoffelSourceWall

/-!
# Exact strict-frontier source-wall integrability gate

At an occupied shifted-Xi strict frontier, the literal adaptive arithmetic numerator is continuous
and interval integrable across the endpoint.  The completed Christoffel wall is nevertheless not
locally integrable: the numerator stays strictly positive while the newborn admission norm
collapses at least linearly.

This module packages the resulting exact Frankenstein interface.  Local integrability of every
occupied strict-frontier wall is unconditionally equivalent to RH.  Thus a cross-route BV or
source-regularity theorem must exclude the endogenous admission zero (or annihilate its numerator);
ordinary regularity of the literal source numerator is already available and is insufficient.
-/

open Matrix Polynomial Set
open MeasureTheory

namespace RHTower

noncomputable section

/-- The literal adaptive source numerator is continuous on every compact interval beginning at an
occupied strict frontier.  The singularity belongs only to subsequent division by the newborn
admission norm. -/
theorem continuousOn_xiShiftedCanonicalAdmissionAdaptiveShear_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {b : ℝ} (_hb : xiShiftedHigherBlockTerminalFrontier (n + 1) ≤ b) :
    ContinuousOn
      (fun v => xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1))
      (Icc (xiShiftedHigherBlockTerminalFrontier (n + 1)) b) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hface :=
    xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  intro v hv
  have hvpos : 0 < v := lt_of_lt_of_le hy hv.1
  have hhead : (xiShiftedMomentHankelMatrix v (n + 1)).PosDef := by
    rcases hv.1.eq_or_lt with rfl | hyv
    · exact xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
    · have hfull : (HTGeometry.momentHankelMatrix
          (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef := by
        simpa only [y, Nat.add_assoc] using
          (xiShiftedHigherBlock_posDef_of_terminalFrontier_lt
            (n := n + 1) hvpos.le hyv)
      exact xiShiftedMomentHankel_posDef_of_le (by omega) hfull
  have hcont := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
    hvpos (n + 1) (ne_of_gt hhead.det_pos)
  have hcont' : ContinuousAt
      (fun u => xiShiftedCanonicalAdmissionAdaptiveShear u (n + 1)) v := by
    simpa only [xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using hcont
  exact hcont'.continuousWithinAt

/-- The exact rational--Gamma/von-Mangoldt adaptive numerator is interval integrable across every
occupied strict frontier.  This is the strongest regularity conclusion available before dividing
by the vanishing Christoffel admission scale. -/
theorem intervalIntegrable_xiShiftedCanonicalAdmissionAdaptiveShear_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    {b : ℝ} (hb : xiShiftedHigherBlockTerminalFrontier (n + 1) ≤ b) :
    IntervalIntegrable
      (fun v => xiShiftedCanonicalAdmissionAdaptiveShear v (n + 1))
      volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b := by
  have hcont :=
    continuousOn_xiShiftedCanonicalAdmissionAdaptiveShear_at_strict_frontier
      hne hstrict hb
  exact (uIcc_of_le hb ▸ hcont).intervalIntegrable

/-- Proposed cross-route producer: every occupied strict-frontier exact Christoffel source wall is
locally integrable on a nontrivial right interval. -/
def XiShiftedAllStrictFrontierSourceWallsLocallyIntegrable : Prop :=
  ∀ n : ℕ,
    (xiShiftedHigherBlockFailureSet n).Nonempty →
    xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1) →
    ∃ b : ℝ,
      xiShiftedHigherBlockTerminalFrontier (n + 1) < b ∧
      IntervalIntegrable
        (fun v => xiShiftedCanonicalAdmissionChristoffelSourceWall v (n + 1))
        volume (xiShiftedHigherBlockTerminalFrontier (n + 1)) b

/-- RH makes the all-frontier local-integrability law true because no shifted-Hankel failure set,
and hence no occupied strict frontier, remains. -/
theorem xiShiftedAllStrictFrontierSourceWallsLocallyIntegrable_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiShiftedAllStrictFrontierSourceWallsLocallyIntegrable := by
  intro n hne _hstrict
  exfalso
  rw [xiShiftedHigherBlockFailureSet_eq_empty_of_riemannHypothesis hRH n] at hne
  exact Set.not_nonempty_empty hne

/-- Any independent theorem placing every exact occupied strict-frontier source wall in local
`L¹` rules out the false-RH cofinal frontier phase. -/
theorem riemannHypothesis_of_xiShiftedAllStrictFrontierSourceWallsLocallyIntegrable
    (hlocal : XiShiftedAllStrictFrontierSourceWallsLocallyIntegrable) :
    RiemannHypothesis := by
  by_contra hnotRH
  obtain ⟨n, hne, _hA, hstrict, _hnext⟩ :=
    exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis hnotRH 0
  obtain ⟨b, hb, hint⟩ := hlocal n hne hstrict
  exact
    (not_intervalIntegrable_xiShiftedCanonicalAdmissionChristoffelSourceWall_at_strict_frontier
      hne hstrict hb) hint

/-- **Exact integrability classification.**  Local integrability of the exact adaptive quotient at
every possible strict frontier is neither generic source smoothness nor an auxiliary estimate: it
is exactly RH. -/
theorem riemannHypothesis_iff_xiShiftedAllStrictFrontierSourceWallsLocallyIntegrable :
    RiemannHypothesis ↔
      XiShiftedAllStrictFrontierSourceWallsLocallyIntegrable := by
  constructor
  · exact xiShiftedAllStrictFrontierSourceWallsLocallyIntegrable_of_riemannHypothesis
  · exact riemannHypothesis_of_xiShiftedAllStrictFrontierSourceWallsLocallyIntegrable

end

end RHTower
