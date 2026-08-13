import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveMixedSourceAction
import GaloisForLFunctions.RHTower.XiShiftedProjectiveAdjacentMeanResetBarrier

/-!
# Adaptive mixed arithmetic source pays hyperbolic degree reset

Ordinary packet variance does not control reciprocal projective-clock reset: the reset metric has
the structurally necessary denominator `U_n² U_(n+1)²`.  This module proves that the literal
newborn adaptive mixed/completed `P^sharp` source action pays exactly this corrected hyperbolic
transport.

The key reserve is stronger than a generic reset barrier.  Newborn cumulative Jacobi dissipation
minus packet-energy increment is the sum of old packet energy, newborn squared flux, and positive
Jacobi-edge inventory.  Consequently the source action strictly dominates the energy increment.
Combining this with the exact online-variance identity gives a division-free hyperbolic clock law,
and terminal-chamber Riccati positivity discharges both mean-nonvanishing conditions on every
physical right ray above a canonical terminal frontier.
-/

open Matrix
open scoped BigOperators

namespace RHTower
namespace XiShiftedCanonicalAdmission

noncomputable section

/-- Weighted projective packet energy is nonnegative without any moment-positivity premise. -/
theorem projectiveAdmissionPacketEnergy_nonneg (s : ℕ → ℝ) (n : ℕ) :
    0 ≤ projectiveAdmissionPacketEnergy s n := by
  unfold projectiveAdmissionPacketEnergy
  have hsum : 0 ≤ ∑ j ∈ Finset.range n,
      (HTGeometry.monicOrthoAlpha s j - projectiveAdmissionPacketMean s n) ^ 2 := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

/-- Exact source reserve behind hyperbolic degree transport.  Besides the old packet energy, all
remaining terms are newborn flux or positive Jacobi-edge inventory. -/
theorem cumulativeJacobiDissipation_sub_packetEnergyIncrement_eq_hyperbolicReserve
    (y : ℝ) (n : ℕ) :
    let s := fun k => (xiShiftedReciprocalMoment y k).re
    xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y (n + 1) -
        (projectiveAdmissionPacketEnergy s (n + 1) -
          projectiveAdmissionPacketEnergy s n) =
      projectiveAdmissionPacketEnergy s n +
        projectiveAdmissionPacketFlux s (n + 1) ^ 2 /
          (2 * ((n + 1 : ℕ) : ℝ) + 1) +
        4 * (∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j) +
        2 * (n + 2 : ℝ) *
          (HTGeometry.monicOrthoBeta s (n + 1) +
            HTGeometry.monicOrthoBeta s (n + 2)) := by
  dsimp only
  rw [xiShiftedCanonicalAdmissionCumulativeJacobiDissipation,
    projectiveAdmissionPacketEnergy_eq]
  push_cast
  ring

/-- Newborn Jacobi dissipation strictly dominates adjacent packet-energy creation. -/
theorem packetEnergyIncrement_lt_cumulativeJacobiDissipation
    {y : ℝ} {n : ℕ}
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 3)).PosDef) :
    projectiveAdmissionPacketEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) (n + 1) -
        projectiveAdmissionPacketEnergy
          (fun k => (xiShiftedReciprocalMoment y k).re) n <
      xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y (n + 1) := by
  let s := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hreserve :=
    cumulativeJacobiDissipation_sub_packetEnergyIncrement_eq_hyperbolicReserve y n
  have henergy : 0 ≤ projectiveAdmissionPacketEnergy s n :=
    projectiveAdmissionPacketEnergy_nonneg s n
  have hflux : 0 ≤ projectiveAdmissionPacketFlux s (n + 1) ^ 2 /
      (2 * ((n + 1 : ℕ) : ℝ) + 1) := by positivity
  have hsumBeta : 0 ≤
      ∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j := by
    apply Finset.sum_nonneg
    intro j hj
    rcases j with _ | j
    · simp [HTGeometry.monicOrthoBeta]
    · exact (HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by
        have := Finset.mem_range.mp hj
        omega)).le
  have hbeta1 : 0 < HTGeometry.monicOrthoBeta s (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  have hbeta2 : 0 < HTGeometry.monicOrthoBeta s (n + 2) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  have hterminal : 0 < 2 * (n + 2 : ℝ) *
      (HTGeometry.monicOrthoBeta s (n + 1) +
        HTGeometry.monicOrthoBeta s (n + 2)) := by positivity
  change projectiveAdmissionPacketEnergy s (n + 1) -
      projectiveAdmissionPacketEnergy s n <
    xiShiftedCanonicalAdmissionCumulativeJacobiDissipation y (n + 1)
  rw [← sub_pos]
  rw [hreserve]
  have hbetaSum : 0 ≤ 4 *
      (∑ j ∈ Finset.range (n + 1), HTGeometry.monicOrthoBeta s j) := by positivity
  exact add_pos_of_nonneg_of_pos
    (add_nonneg (add_nonneg henergy hflux) hbetaSum) hterminal

/-- Literal adaptive mixed/completed newborn source action strictly dominates packet-energy
creation. -/
theorem packetEnergyIncrement_lt_adaptiveMixedCompletedSourceAction
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef) :
    projectiveAdmissionPacketEnergy (xiShiftedRealMomentSequence w) (n + 1) -
        projectiveAdmissionPacketEnergy (xiShiftedRealMomentSequence w) n <
      xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1) := by
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction_eq_cumulativeJacobiDissipation
      hw (by omega : 0 < n + 1) hH
  rw [hsource]
  exact packetEnergyIncrement_lt_cumulativeJacobiDissipation hH

/-- Generic packet mean is the actual normalized canonical Jacobi flux in a positive block. -/
theorem projectiveAdmissionPacketMean_eq_renormalizedJacobiFlux
    {y : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef) :
    projectiveAdmissionPacketMean
        (fun k => (xiShiftedReciprocalMoment y k).re) n =
      xiShiftedCanonicalAdmissionRenormalizedJacobiFlux y n := by
  rw [projectiveAdmissionPacketMean,
    xiShiftedCanonicalAdmissionRenormalizedJacobiFlux,
    xiShiftedCanonicalAdmissionCumulativeJacobiFlux_eq_trace hn hH]
  rfl

/-- **Arithmetic hyperbolic reset law.**  Literal newborn source action pays squared reciprocal
clock reset after multiplication by the forced adjacent-mean metric weight. -/
theorem adaptiveMixedCompletedSourceAction_pays_hyperbolicClockReset
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 3)).PosDef)
    (hmean : projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) n ≠ 0)
    (hmeanNext : projectiveAdmissionPacketMean
      (xiShiftedRealMomentSequence w) (n + 1) ≠ 0) :
    (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) n ^ 2 *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) (n + 1) ^ 2 *
        (projectiveAdmissionScalarClock (w ^ 2) (xiShiftedRealMomentSequence w) (n + 1) -
          projectiveAdmissionScalarClock (w ^ 2) (xiShiftedRealMomentSequence w) n) ^ 2 <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1) := by
  let s := xiShiftedRealMomentSequence w
  let μ := projectiveAdmissionPacketMean s n
  let ν := projectiveAdmissionPacketMean s (n + 1)
  have hμ : μ ≠ 0 := by simpa only [μ, s] using hmean
  have hν : ν ≠ 0 := by simpa only [ν, s] using hmeanNext
  have henergy := projectiveAdmissionPacketEnergy_succ_sub_ge s n
  have hsource := packetEnergyIncrement_lt_adaptiveMixedCompletedSourceAction hw hn hH
  have hclock := projectiveAdmissionScalarClock_succ_sub (w ^ 2) s n hmean hmeanNext
  change projectiveAdmissionScalarClock (w ^ 2) s (n + 1) -
      projectiveAdmissionScalarClock (w ^ 2) s n = -((ν - μ) / (μ * ν)) at hclock
  have hcancel :
      (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) * μ ^ 2 * ν ^ 2 *
          (projectiveAdmissionScalarClock (w ^ 2) s (n + 1) -
            projectiveAdmissionScalarClock (w ^ 2) s n) ^ 2 =
        (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) * (ν - μ) ^ 2 := by
    rw [hclock]
    field_simp [hμ, hν]
  change (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) * μ ^ 2 * ν ^ 2 *
      (projectiveAdmissionScalarClock (w ^ 2) s (n + 1) -
        projectiveAdmissionScalarClock (w ^ 2) s n) ^ 2 <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1)
  rw [hcancel]
  change (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) / 2 * (ν - μ) ^ 2 ≤ _ at henergy
  change projectiveAdmissionPacketEnergy s (n + 1) -
      projectiveAdmissionPacketEnergy s n < _ at hsource
  nlinarith

/-- On a complete terminal chamber, Riccati contraction forces both adjacent packet means
positive, removing nonvanishing assumptions from the arithmetic hyperbolic reset law. -/
theorem adaptiveMixedCompletedSourceAction_pays_hyperbolicClockReset_of_terminalChamber
    {A w : ℝ} (hA : 0 ≤ A) (hw : 1 / 2 < w) (hAw : A < w ^ 2)
    {n : ℕ} (hn : 0 < n)
    (hchamber : ∀ v, A < v →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 3)).PosDef) :
    (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) n ^ 2 *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) (n + 1) ^ 2 *
        (projectiveAdmissionScalarClock (w ^ 2) (xiShiftedRealMomentSequence w) (n + 1) -
          projectiveAdmissionScalarClock (w ^ 2) (xiShiftedRealMomentSequence w) n) ^ 2 <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1) := by
  have hH := hchamber (w ^ 2) hAw
  have hchamberCurrent : ∀ v, A < v →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment v k).re) (n + 2)).PosDef := by
    intro v hv
    exact xiShiftedMomentHankel_posDef_of_le (by omega) (hchamber v hv)
  have hHcurrent := hchamberCurrent (w ^ 2) hAw
  have hmeanPos : 0 < projectiveAdmissionPacketMean
      (xiShiftedRealMomentSequence w) n := by
    rw [show xiShiftedRealMomentSequence w =
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) from rfl,
      projectiveAdmissionPacketMean_eq_renormalizedJacobiFlux hn hHcurrent]
    exact xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber
      hA hAw hn hchamberCurrent
  have hmeanNextPos : 0 < projectiveAdmissionPacketMean
      (xiShiftedRealMomentSequence w) (n + 1) := by
    rw [show xiShiftedRealMomentSequence w =
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) from rfl,
      projectiveAdmissionPacketMean_eq_renormalizedJacobiFlux (by omega) hH]
    exact xiShiftedCanonicalAdmissionRenormalizedJacobiFlux_pos_of_terminalChamber
      hA hAw (by omega) hchamber
  exact adaptiveMixedCompletedSourceAction_pays_hyperbolicClockReset
    hw hn hH hmeanPos.ne' hmeanNextPos.ne'

/-- Every physical right ray above an actual canonical terminal frontier satisfies the literal
source-paid hyperbolic reset law. -/
theorem adaptiveMixedCompletedSourceAction_pays_hyperbolicClockReset_above_terminalFrontier
    {n : ℕ} (hn : 0 < n)
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1))
    {v : ℝ} (hv : xiShiftedHigherBlockTerminalFrontier (n + 1) < v) :
    let w := Real.sqrt v
    (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3) *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) n ^ 2 *
        projectiveAdmissionPacketMean (xiShiftedRealMomentSequence w) (n + 1) ^ 2 *
        (projectiveAdmissionScalarClock v (xiShiftedRealMomentSequence w) (n + 1) -
          projectiveAdmissionScalarClock v (xiShiftedRealMomentSequence w) n) ^ 2 <
      2 * xiShiftedCanonicalAdmissionAdaptiveMixedCompletedSourceAction w (n + 1) := by
  dsimp only
  have hvpos : 0 < v := lt_trans (lt_trans (by norm_num) hphysical) hv
  have hsq : (Real.sqrt v) ^ 2 = v := Real.sq_sqrt hvpos.le
  have hw : 1 / 2 < Real.sqrt v := by nlinarith [Real.sqrt_nonneg v]
  have hA : 0 ≤ xiShiftedHigherBlockTerminalFrontier (n + 1) := by
    linarith
  have hchamber : ∀ z, xiShiftedHigherBlockTerminalFrontier (n + 1) < z →
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment z k).re) (n + 3)).PosDef := by
    intro z hz
    have hz0 : 0 ≤ z := le_trans hA hz.le
    exact xiShiftedHigherBlock_posDef_of_terminalFrontier_lt hz0 hz
  have h :=
    adaptiveMixedCompletedSourceAction_pays_hyperbolicClockReset_of_terminalChamber
      hA hw (by simpa only [hsq] using hv) hn hchamber
  simpa only [hsq] using h

end
end XiShiftedCanonicalAdmission
end RHTower
