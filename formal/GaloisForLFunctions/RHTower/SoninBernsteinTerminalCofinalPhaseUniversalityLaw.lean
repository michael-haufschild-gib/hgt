import GaloisForLFunctions.RHTower.SoninCoupledQuantumBernsteinApproximationRH
import GaloisForLFunctions.RHTower.XiTerminalAnalyticSourceUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchCofinalOrientationChargeUniversalityLaw

/-!
# Coupled-Sonin Bernstein control governs every terminal and cofinal Xi phase

The three hypothesis-free coupled-Sonin Bernstein approximation criteria were previously terminal
producers of RH.  This file transports their common conclusion through both the fourteen-chart
terminal analytic-source atlas and the schedule-independent cofinal orientation-charge atlas.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Any one of the three concrete cofinal coupled-Sonin Bernstein controls: bounded squared
discrepancy, bounded `L¹` discrepancy, or the natural inverse-degree quadratic bound. -/
def SoninCoupledBernsteinCofinalControl
    (d : ℕ → ℕ) (a : ℕ → SoninPositiveAperture) : Prop :=
  (∃ E : ℝ, ∀ j,
    bernsteinCoefficientSquareDiscrepancyAtDefectDegree
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment)
      (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ E) ∨
  (∃ C : ℝ, ∀ j,
    bernsteinCoefficientL1DiscrepancyAtDefectDegree
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment)
      (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ C) ∨
  (∃ C : ℝ, 0 ≤ C ∧ ∀ j, (d j + 2 : ℝ) *
    bernsteinCoefficientSquareDiscrepancyAtDefectDegree
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment)
      (soninAllPrimeCoupledRenyiReplicaMoment (a j)) (d j) ≤ C ^ 2)

/-- Simultaneous realization of the terminal analytic-source atlas, exact orientation phase, and
all cofinal prime--archimedean thermal regimes. -/
def SoninBernsteinTerminalCofinalPhaseUniversalCertificate
    (Lrect : ℝ) (N : ℕ) (eta Lsmooth : ℝ)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (D : ℕ → ℕ) (degreeSet : Set ℕ)
    (size cold : ℕ → ℕ) : Prop :=
  XiTerminalAnalyticSourceUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet ∧
  xiThermalOrientationEnergy = 0 ∧
  CofinalHausdorffBernsteinNegativeMassVanishing
      primeArchEndpointHausdorffRadius normalizedPrimeArchMoment ∧
  ContinuedPrimeArchPositiveFrequencyAbove 4 ∧
  Tendsto
      (fun j : ℕ =>
        Real.log (xiThermalProjectiveColdTruncation (size j) (cold j)) /
          (cold j : ℝ))
      atTop (nhds 0) ∧
  (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ j : ℕ in atTop,
    xiThermalProjectiveColdTruncation (size j) (cold j) ≤
      Real.exp (epsilon * (cold j : ℝ))) ∧
  (∃ C : ℝ, ∃ᶠ j : ℕ in atTop,
    xiThermalProjectiveColdTruncation (size j) (cold j) ≤ C)

/-- **Coupled-Sonin terminal/cofinal phase universality.**  Along any cofinal Bernstein-degree
schedule, any one of the three concrete coupled-Sonin approximation controls forces every
terminal analytic-source chart and every cofinal thermal phase for arbitrary cofinal size and
cooling schedules. -/
theorem soninCoupledBernsteinControl_forces_terminalCofinalPhaseUniversality
    {d : ℕ → ℕ} {a : ℕ → SoninPositiveAperture}
    (hd : Tendsto d atTop atTop)
    (hcontrol : SoninCoupledBernsteinCofinalControl d a)
    {Lrect : ℝ} (hLrect : 0 < Lrect) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ Lrect ≤ Real.log n / 2)
    {eta Lsmooth : ℝ} (heta : 0 < eta) (hwindow : eta < Lsmooth - eta)
    (P : ℕ → XiSeparatedContinuedCauchyPacket)
    (hP : IsRectangularSeparatedSourceSection Lrect P)
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    {degreeSet : Set ℕ} (hdegreeSet : degreeSet.Infinite)
    (size cold : ℕ → ℕ)
    (hsize : Tendsto size atTop atTop)
    (hcold : Tendsto cold atTop atTop) :
    SoninBernsteinTerminalCofinalPhaseUniversalCertificate
      Lrect N eta Lsmooth P D degreeSet size cold := by
  have hRH : RiemannHypothesis := by
    rcases hcontrol with hsq | hl1 | hscaled
    · rcases hsq with ⟨E, hE⟩
      exact
        riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinSquareDiscrepancy_bounded
          d a E hd hE
    · rcases hl1 with ⟨C, hC⟩
      exact
        riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinL1Discrepancy_bounded
          d a C hd hC
    · rcases hscaled with ⟨C, hC, henergy⟩
      exact
        riemannHypothesis_of_cofinal_soninCoupledRenyi_bernsteinSquareDiscrepancy
          d a C hC hd henergy
  have hterminal :
      XiTerminalAnalyticSourceUniversalCertificate
        Lrect N eta Lsmooth P D degreeSet :=
    (riemannHypothesis_iff_terminalAnalyticSourceUniversalCertificate
      hLrect hN heta hwindow P hP hD hdegreeSet).1 hRH
  have hzero : xiThermalOrientationEnergy = 0 :=
    xiThermalOrientationEnergy_eq_zero_iff_rh.2 hRH
  have hphase :=
    primeArchCofinalOrientationChargeUniversality size cold hsize hcold
  exact ⟨hterminal, hzero,
    hphase.1.2 hzero,
    hphase.2.1.2 hzero,
    hphase.2.2.1.1 hzero,
    hphase.2.2.2.1.1 hzero,
    hphase.2.2.2.2.1 hzero⟩

end

end RHTower
