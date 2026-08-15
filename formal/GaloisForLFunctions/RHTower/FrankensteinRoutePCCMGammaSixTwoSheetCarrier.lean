import GaloisForLFunctions.RHTower.FrankensteinRoutePTailFluxCCMThirdJetBridge
import GaloisForLFunctions.RHTower.DeningerGammaSixCofinalSingularGraphSoninTransport

/-!
# Route-P/CCM tail current on a two-sheet Gamma-six singular carrier

The one-dimensional Gamma-six singular trace retains total packet mass.  It therefore kills
the centered, zero-mass clock directions on which CCM's first transverse cubic jet lives.  This
module keeps two reflected copies of that exact source graph and separates their mass and
orientation traces.

Antisymmetric actual-Gamma averages have mass trace zero and orientation trace one at every
finite stage.  Their ambient cofinal `ell^2` coordinates disappear, while the graph vectors
converge to a nonzero vertical orientation class.  Scaling this class by one P-G189 primitive
tail-flux coefficient preserves its prime/depth label.  The same class has two exact readouts:

* its orientation trace is the coefficient of the P-tail/CCM transverse third-jet matrix;
* its two-sheet actual-Gamma transport is that coefficient times the fixed Sonin horizontal
  detector, and vanishes exactly at neutral horizontal grade.

Thus the scalar-trace blindness is removed without collapsing reflection orientations or using
divisor data in the source carrier.  This constructs a coefficient-faithful, moment-neutral
pre-scalar carrier; it does not assert the remaining arithmetic Stokes annihilation.
-/

open Complex Filter Topology Matrix

namespace RHTower

noncomputable section

abbrev FrankensteinTwoSheetGraph :=
  WithLp 2 (DeningerGammaSixCofinalSingularGraph ×
    DeningerGammaSixCofinalSingularGraph)

def frankensteinTwoSheetFst :
    FrankensteinTwoSheetGraph →L[ℂ] DeningerGammaSixCofinalSingularGraph :=
  WithLp.fstL 2 ℂ _ _

def frankensteinTwoSheetSnd :
    FrankensteinTwoSheetGraph →L[ℂ] DeningerGammaSixCofinalSingularGraph :=
  WithLp.sndL 2 ℂ _ _

def frankensteinTwoSheetMassTrace : FrankensteinTwoSheetGraph →L[ℂ] ℂ :=
  deningerGammaSixCofinalGraphTrace.comp frankensteinTwoSheetFst +
    deningerGammaSixCofinalGraphTrace.comp frankensteinTwoSheetSnd

def frankensteinTwoSheetOrientationTrace : FrankensteinTwoSheetGraph →L[ℂ] ℂ :=
  deningerGammaSixCofinalGraphTrace.comp frankensteinTwoSheetFst -
    deningerGammaSixCofinalGraphTrace.comp frankensteinTwoSheetSnd

def frankensteinTwoSheetOrientationVector : FrankensteinTwoSheetGraph :=
  WithLp.toLp 2
    (((1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector),
      ((-1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector))

@[simp] theorem frankensteinTwoSheetMassTrace_orientationVector :
    frankensteinTwoSheetMassTrace frankensteinTwoSheetOrientationVector = 0 := by
  simp [frankensteinTwoSheetMassTrace, frankensteinTwoSheetFst,
    frankensteinTwoSheetSnd, frankensteinTwoSheetOrientationVector]
  norm_num

@[simp] theorem frankensteinTwoSheetOrientationTrace_orientationVector :
    frankensteinTwoSheetOrientationTrace frankensteinTwoSheetOrientationVector = 1 := by
  simp [frankensteinTwoSheetOrientationTrace, frankensteinTwoSheetFst,
    frankensteinTwoSheetSnd, frankensteinTwoSheetOrientationVector]
  ring

def frankensteinTwoSheetFiniteOrientationPacket
    (n : ℕ) : FrankensteinTwoSheetGraph :=
  WithLp.toLp 2
    (((1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
        (deningerGammaSixCofinalAveragingPacket n)),
      ((-1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
        (deningerGammaSixCofinalAveragingPacket n)))

@[simp] theorem frankensteinTwoSheetMassTrace_finiteOrientationPacket
    (n : ℕ) :
    frankensteinTwoSheetMassTrace
        (frankensteinTwoSheetFiniteOrientationPacket n) = 0 := by
  have ht : deningerGammaSixCofinalGraphTrace
      (deningerGammaSixCofinalFiniteGraphAdmission
        (deningerGammaSixCofinalAveragingPacket n)) = 1 := by
    change deningerGammaSixCofinalFinitePacketTrace
      (deningerGammaSixCofinalAveragingPacket n) = 1
    exact deningerGammaSixCofinalFinitePacketTrace_averagingPacket n
  simp [frankensteinTwoSheetMassTrace, frankensteinTwoSheetFst,
    frankensteinTwoSheetSnd, frankensteinTwoSheetFiniteOrientationPacket, ht]
  norm_num

@[simp] theorem frankensteinTwoSheetOrientationTrace_finiteOrientationPacket
    (n : ℕ) :
    frankensteinTwoSheetOrientationTrace
        (frankensteinTwoSheetFiniteOrientationPacket n) = 1 := by
  have ht : deningerGammaSixCofinalGraphTrace
      (deningerGammaSixCofinalFiniteGraphAdmission
        (deningerGammaSixCofinalAveragingPacket n)) = 1 := by
    change deningerGammaSixCofinalFinitePacketTrace
      (deningerGammaSixCofinalAveragingPacket n) = 1
    exact deningerGammaSixCofinalFinitePacketTrace_averagingPacket n
  simp [frankensteinTwoSheetOrientationTrace, frankensteinTwoSheetFst,
    frankensteinTwoSheetSnd, frankensteinTwoSheetFiniteOrientationPacket, ht]
  norm_num

theorem tendsto_frankensteinTwoSheetFiniteOrientationPacket :
    Tendsto frankensteinTwoSheetFiniteOrientationPacket atTop
      (nhds frankensteinTwoSheetOrientationVector) := by
  have h :=
    tendsto_deningerGammaSixCofinalFiniteGraphAdmission_averagingPacket
  have hpair : Tendsto
      (fun n =>
        (((1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
            (deningerGammaSixCofinalAveragingPacket n)),
          ((-1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
            (deningerGammaSixCofinalAveragingPacket n))))
      atTop
      (nhds
        (((1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector),
          ((-1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector))) := by
    simpa only [nhds_prod_eq] using
      (h.const_smul (1 / 2 : ℂ)).prodMk (h.const_smul (-1 / 2 : ℂ))
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    DeningerGammaSixCofinalSingularGraph
    DeningerGammaSixCofinalSingularGraph).symm.continuous.tendsto _).comp hpair

def frankensteinTwoSheetPhysicalTransport (g : ℝ) :
    FrankensteinTwoSheetGraph →L[ℂ] DeningerGammaSixSoninPhysicalOperator :=
  (deningerGammaSixCofinalGraphPhysicalTransport g).comp
      frankensteinTwoSheetFst -
    (deningerGammaSixCofinalGraphPhysicalTransport g).comp
      frankensteinTwoSheetSnd

@[simp] theorem frankensteinTwoSheetPhysicalTransport_orientationVector
    (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        frankensteinTwoSheetOrientationVector =
      deningerGammaSixFixedSoninPhysicalReceiver g := by
  change
    deningerGammaSixCofinalGraphPhysicalTransport g
        ((1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector) -
      deningerGammaSixCofinalGraphPhysicalTransport g
        ((-1 / 2 : ℂ) • deningerGammaSixCofinalGraphSingularVector) = _
  rw [map_smul, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_singularVector]
  rw [← sub_smul]
  norm_num

@[simp] theorem frankensteinTwoSheetPhysicalTransport_finiteOrientationPacket
    (g : ℝ) (n : ℕ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinTwoSheetFiniteOrientationPacket n) =
      deningerGammaSixFixedSoninPhysicalReceiver g := by
  change
    deningerGammaSixCofinalGraphPhysicalTransport g
        ((1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
          (deningerGammaSixCofinalAveragingPacket n)) -
      deningerGammaSixCofinalGraphPhysicalTransport g
        ((-1 / 2 : ℂ) • deningerGammaSixCofinalFiniteGraphAdmission
          (deningerGammaSixCofinalAveragingPacket n)) = _
  rw [map_smul, map_smul,
    deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph,
    deningerGammaSixCofinalFiniteActualGammaTransport_averagingPacket]
  rw [← sub_smul]
  norm_num

def frankensteinRoutePTailFluxTwoSheetCell
    (pe : Nat.Primes × ℕ) : FrankensteinTwoSheetGraph :=
  (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
    frankensteinTwoSheetOrientationVector

def frankensteinRoutePTailFluxTwoSheetFiniteCell
    (pe : Nat.Primes × ℕ) (n : ℕ) : FrankensteinTwoSheetGraph :=
  (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
    frankensteinTwoSheetFiniteOrientationPacket n

theorem tendsto_frankensteinRoutePTailFluxTwoSheetFiniteCell
    (pe : Nat.Primes × ℕ) :
    Tendsto (frankensteinRoutePTailFluxTwoSheetFiniteCell pe) atTop
      (nhds (frankensteinRoutePTailFluxTwoSheetCell pe)) := by
  exact tendsto_frankensteinTwoSheetFiniteOrientationPacket.const_smul _

@[simp] theorem frankensteinTwoSheetMassTrace_tailFluxCell
    (pe : Nat.Primes × ℕ) :
    frankensteinTwoSheetMassTrace
        (frankensteinRoutePTailFluxTwoSheetCell pe) = 0 := by
  simp [frankensteinRoutePTailFluxTwoSheetCell]

@[simp] theorem frankensteinTwoSheetOrientationTrace_tailFluxCell
    (pe : Nat.Primes × ℕ) :
    frankensteinTwoSheetOrientationTrace
        (frankensteinRoutePTailFluxTwoSheetCell pe) =
      routePPrimitiveBurnolApertureDefectFlux pe := by
  simp [frankensteinRoutePTailFluxTwoSheetCell]

theorem frankensteinTwoSheetPhysicalTransport_tailFluxCell
    (pe : Nat.Primes × ℕ) (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinRoutePTailFluxTwoSheetCell pe) =
      (routePPrimitiveBurnolApertureDefectFlux pe : ℂ) •
        deningerGammaSixFixedSoninPhysicalReceiver g := by
  rw [frankensteinRoutePTailFluxTwoSheetCell, map_smul,
    frankensteinTwoSheetPhysicalTransport_orientationVector]

theorem frankensteinTwoSheetPhysicalTransport_tailFluxCell_eq_zero_iff
    (pe : Nat.Primes × ℕ) (g : ℝ) :
    frankensteinTwoSheetPhysicalTransport g
        (frankensteinRoutePTailFluxTwoSheetCell pe) = 0 ↔ g = 0 := by
  rw [frankensteinTwoSheetPhysicalTransport_tailFluxCell,
    smul_eq_zero, Complex.ofReal_eq_zero,
    deningerGammaSixFixedSoninPhysicalReceiver_eq_zero_iff]
  simp only [(routePPrimitiveBurnolApertureDefectFlux_pos pe).ne', false_or]

def frankensteinTwoSheetCCMThirdJetReadout
    (N : ℕ) (z : FrankensteinTwoSheetGraph) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j => frankensteinTwoSheetOrientationTrace z *
    (ccmGuinandWeilPrimeEntryUniversalThirdJet N i j : ℂ)

theorem frankensteinTwoSheetCCMThirdJetReadout_tailFluxCell
    (pe : Nat.Primes × ℕ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    frankensteinTwoSheetCCMThirdJetReadout N
        (frankensteinRoutePTailFluxTwoSheetCell pe) i j =
      (frankensteinRoutePTailFluxCCMThirdJet {pe} N i j : ℂ) := by
  have hreal :
      frankensteinRoutePTailFluxCCMThirdJet {pe} N i j =
        routePPrimitiveBurnolApertureDefectFlux pe *
          ccmGuinandWeilPrimeEntryUniversalThirdJet N i j := by
    rw [frankensteinRoutePTailFluxCCMThirdJet, Matrix.sum_apply]
    simp [Matrix.smul_apply]
  rw [frankensteinTwoSheetCCMThirdJetReadout,
    frankensteinTwoSheetOrientationTrace_tailFluxCell, hreal]
  norm_cast

end

end RHTower
