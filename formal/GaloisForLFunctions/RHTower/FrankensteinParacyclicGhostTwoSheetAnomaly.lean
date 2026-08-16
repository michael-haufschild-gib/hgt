import GaloisForLFunctions.RHTower.MobiusThetaPhysicalParacyclicSourceNullHomology
import GaloisForLFunctions.RHTower.FrankensteinRoutePCCMGammaSixTwoSheetCarrier

open Complex Matrix GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

def frankensteinParacyclicAnomalyCoefficient
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) : ℂ :=
  ccmRationalAdelicTwoLegCyclicResidue
    (cyclicParacyclicEquivarianceDefect
      ccmRationalAdelicDegreeOneCyclicRotation
      (sourceDaggerNormalizedDegreeOneRotationLinear n (rho : ℂ))
      (ccmMobiusThetaXiJetTwoLegLanding
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho))
      (ccmRationalAdelicOrdinaryPrimeCycleAtom pe.1))

def frankensteinParacyclicAnomalyTailFluxTwoSheetCell
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    FrankensteinTwoSheetGraph :=
  frankensteinParacyclicAnomalyCoefficient n rho pe •
    frankensteinRoutePTailFluxTwoSheetCell pe

theorem frankensteinParacyclicAnomalyCoefficient_eq
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinParacyclicAnomalyCoefficient n rho pe =
      ((deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1) *
        thetaInternalJetLeadingSourceCoefficient rho := by
  rw [frankensteinParacyclicAnomalyCoefficient,
    ccmMobiusThetaTwoLegParacyclicDefect_residue,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, mul_one]

@[simp] theorem frankensteinTwoSheetMassTrace_paracyclicAnomalyTailFluxCell
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinTwoSheetMassTrace
        (frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe) = 0 := by
  simp [frankensteinParacyclicAnomalyTailFluxTwoSheetCell]

@[simp] theorem frankensteinTwoSheetOrientationTrace_paracyclicAnomalyTailFluxCell
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinTwoSheetOrientationTrace
        (frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe) =
      frankensteinParacyclicAnomalyCoefficient n rho pe *
        routePPrimitiveBurnolApertureDefectFlux pe := by
  simp [frankensteinParacyclicAnomalyTailFluxTwoSheetCell]

theorem frankensteinParacyclicAnomalyTailFlux_orientationTrace_eq_cofinalReadout
    (n m : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinTwoSheetOrientationTrace
        (frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe) =
      (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) *
        tateClockCofinalRelativeH1Equiv m
          (ccmMobiusThetaCofinalSourceHomologyLanding n
            (xiSupportMultiplicity rho) m (rho : ℂ)
            (xiSpectralPointSupport rho)
            (ccmRationalAdelicOrdinaryPrimeCycleAtom pe.1)) := by
  have hreadout :
      tateClockCofinalRelativeH1Equiv m
          (ccmMobiusThetaCofinalSourceHomologyLanding n
            (xiSupportMultiplicity rho) m (rho : ℂ)
            (xiSpectralPointSupport rho)
            (ccmRationalAdelicOrdinaryPrimeCycleAtom pe.1)) =
        frankensteinParacyclicAnomalyCoefficient n rho pe := by
    rw [ccmMobiusThetaCofinalSourceHomologyLanding_readout_eq_physicalDefect]
    rfl
  rw [frankensteinTwoSheetOrientationTrace_paracyclicAnomalyTailFluxCell,
    hreadout]
  exact mul_comm _ _

theorem frankensteinTwoSheetPhysicalTransport_paracyclicAnomalyTailFluxCell
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe) =
      (frankensteinParacyclicAnomalyCoefficient n rho pe *
        routePPrimitiveBurnolApertureDefectFlux pe) •
          deningerGammaSixFixedSoninPhysicalReceiver g := by
  rw [frankensteinParacyclicAnomalyTailFluxTwoSheetCell, map_smul,
    frankensteinTwoSheetPhysicalTransport_tailFluxCell, smul_smul]

theorem frankensteinTwoSheetCCMThirdJetReadout_paracyclicAnomalyTailFluxCell
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ)
    (N : ℕ) (i j : Fin (2 * N + 1)) :
    frankensteinTwoSheetCCMThirdJetReadout N
        (frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe) i j =
      frankensteinParacyclicAnomalyCoefficient n rho pe *
        (frankensteinRoutePTailFluxCCMThirdJet {pe} N i j : ℂ) := by
  rw [frankensteinTwoSheetCCMThirdJetReadout,
    frankensteinTwoSheetOrientationTrace_paracyclicAnomalyTailFluxCell,
    show (frankensteinRoutePTailFluxCCMThirdJet {pe} N i j : ℂ) =
        (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) *
          (ccmGuinandWeilPrimeEntryUniversalThirdJet N i j : ℂ) by
      rw [frankensteinRoutePTailFluxCCMThirdJet, Matrix.sum_apply]
      simp [Matrix.smul_apply]]
  ring

theorem frankensteinParacyclicAnomalyTailFluxTwoSheetCell_eq_zero_iff
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) :
    frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hcell
    have htrace := congrArg frankensteinTwoSheetOrientationTrace hcell
    rw [frankensteinTwoSheetOrientationTrace_paracyclicAnomalyTailFluxCell,
      map_zero] at htrace
    have hflux : (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) ≠ 0 := by
      exact_mod_cast (routePPrimitiveBurnolApertureDefectFlux_pos pe).ne'
    have hcoeff : frankensteinParacyclicAnomalyCoefficient n rho pe = 0 :=
      (mul_eq_zero.mp htrace).resolve_right hflux
    rw [frankensteinParacyclicAnomalyCoefficient_eq] at hcoeff
    have hc : thetaInternalJetLeadingSourceCoefficient rho ≠ 0 :=
      thetaInternalJetLeadingSourceCoefficient_ne_zero rho
    have hgainC : (deningerHalfDensityMateGain n (rho : ℂ) : ℂ) - 1 = 0 :=
      (mul_eq_zero.mp hcoeff).resolve_right hc
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
      exact_mod_cast sub_eq_zero.mp hgainC
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mp hgain
  · intro hline
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mpr hline
    rw [frankensteinParacyclicAnomalyTailFluxTwoSheetCell,
      frankensteinParacyclicAnomalyCoefficient_eq, hgain]
    norm_num

theorem frankensteinParacyclicAnomalyTailFlux_sameLineCancellation_iff
    (n : ℕ) (rho : XiDivisorSupport) (pe : Nat.Primes × ℕ) (b : ℂ) :
    frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe +
        b • frankensteinRoutePTailFluxTwoSheetCell pe = 0 ↔
      b = -frankensteinParacyclicAnomalyCoefficient n rho pe := by
  constructor
  · intro hcancel
    have htrace := congrArg frankensteinTwoSheetOrientationTrace hcancel
    rw [map_add, map_smul,
      frankensteinTwoSheetOrientationTrace_paracyclicAnomalyTailFluxCell,
      frankensteinTwoSheetOrientationTrace_tailFluxCell, map_zero] at htrace
    have hflux : (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) ≠ 0 := by
      exact_mod_cast (routePPrimitiveBurnolApertureDefectFlux_pos pe).ne'
    have hsum :
        (frankensteinParacyclicAnomalyCoefficient n rho pe + b) *
          (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) = 0 := by
      linear_combination htrace
    have hab := (mul_eq_zero.mp hsum).resolve_right hflux
    linear_combination hab
  · rintro rfl
    rw [frankensteinParacyclicAnomalyTailFluxTwoSheetCell]
    module

def EveryFrankensteinParacyclicAnomalyTailFluxTwoSheetCellVanishes
    (n : ℕ) (pe : Nat.Primes × ℕ) : Prop :=
  ∀ rho : XiDivisorSupport,
    frankensteinParacyclicAnomalyTailFluxTwoSheetCell n rho pe = 0

theorem everyFrankensteinParacyclicAnomalyTailFluxTwoSheetCellVanishes_iff_riemannHypothesis
    {n : ℕ} (hn : 2 ≤ n) (pe : Nat.Primes × ℕ) :
    EveryFrankensteinParacyclicAnomalyTailFluxTwoSheetCellVanishes n pe ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    apply (ccmMobiusThetaEveryPhysicalDefectSourceNullHomologous_iff_riemannHypothesis
      hn pe.1 0).mp
    intro rho
    exact (ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff hn rho pe.1 0).2
      ((frankensteinParacyclicAnomalyTailFluxTwoSheetCell_eq_zero_iff hn rho pe).1
        (hall rho))
  · intro hRH rho
    have hnull :=
      (ccmMobiusThetaEveryPhysicalDefectSourceNullHomologous_iff_riemannHypothesis
        hn pe.1 0).2 hRH rho
    exact (frankensteinParacyclicAnomalyTailFluxTwoSheetCell_eq_zero_iff hn rho pe).2
      ((ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff hn rho pe.1 0).1 hnull)

end

end RHTower
