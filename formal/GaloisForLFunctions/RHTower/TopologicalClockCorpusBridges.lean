import GaloisForLFunctions.RHTower.RiceMeleTopologicalClockApplications
import GaloisForLFunctions.HTGeometry.MarkedHalfCharacterCompactActionLaw
import GaloisForLFunctions.HTGeometry.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.ScaleInnovationPhaseGauge
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.AbelianChernSimons

open scoped BigOperators Matrix
open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

theorem riceMeleNormSq_zero (J delta Delta : ℝ) :
    riceMeleNormSq J delta Delta 0 = Delta ^ (2 : ℕ) + 4 * J ^ (2 : ℕ) := by
  rw [riceMeleNormSq_eq]
  simp
  ring

theorem riceMeleNormSq_pi (J delta Delta : ℝ) :
    riceMeleNormSq J delta Delta Real.pi = Delta ^ (2 : ℕ) + 4 * J ^ (2 : ℕ) * delta ^ (2 : ℕ) := by
  rw [riceMeleNormSq_eq, Real.cos_pi]
  ring

theorem normalizedPump_zoneEdge_minimal (k tau : ℝ) :
    riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) Real.pi ≤
      riceMeleNormSq 1 (normalizedPumpDelta tau) (normalizedPumpMass tau) k := by
  rw [normalizedPump_normSq_decomposition, normalizedPump_normSq_decomposition]
  simp only [Real.cos_pi]
  have hcosSq : Real.cos tau ^ (2 : ℕ) ≤ 1 := by
    nlinarith [Real.neg_one_le_cos tau, Real.cos_le_one tau]
  have hfactor : 0 ≤ 1 - (1 / 4 : ℝ) * Real.cos tau ^ (2 : ℕ) := by nlinarith
  have hbase : 0 ≤ 1 + Real.cos k := by linarith [Real.neg_one_le_cos k]
  nlinarith [mul_nonneg hfactor hbase]

theorem hasDerivAt_riceMeleNormSq (J delta Delta k : ℝ) :
    HasDerivAt (fun q => riceMeleNormSq J delta Delta q)
      (-2 * J ^ (2 : ℕ) * (1 - delta ^ (2 : ℕ)) * Real.sin k) k := by
  have hfun : (fun q => riceMeleNormSq J delta Delta q) =
      fun q => (Delta ^ (2 : ℕ) + 2 * J ^ (2 : ℕ) * (1 + delta ^ (2 : ℕ))) +
        (2 * J ^ (2 : ℕ) * (1 - delta ^ (2 : ℕ))) * Real.cos q := by
    funext q
    rw [riceMeleNormSq_eq]
    ring
  rw [hfun]
  have h := (hasDerivAt_const k
      (Delta ^ (2 : ℕ) + 2 * J ^ (2 : ℕ) * (1 + delta ^ (2 : ℕ)))).add
    ((Real.hasDerivAt_cos k).const_mul (2 * J ^ (2 : ℕ) * (1 - delta ^ (2 : ℕ))))
  have hderiv :
      (0 : ℝ) + (2 * J ^ (2 : ℕ) * (1 - delta ^ (2 : ℕ))) * (-Real.sin k) =
        -2 * J ^ (2 : ℕ) * (1 - delta ^ (2 : ℕ)) * Real.sin k := by ring
  rw [← hderiv]
  exact h

theorem riceMeleNormSq_stationary_zero (J delta Delta : ℝ) :
    deriv (fun q => riceMeleNormSq J delta Delta q) 0 = 0 := by
  rw [(hasDerivAt_riceMeleNormSq J delta Delta 0).deriv]
  simp

theorem riceMeleNormSq_stationary_pi (J delta Delta : ℝ) :
    deriv (fun q => riceMeleNormSq J delta Delta q) Real.pi = 0 := by
  rw [(hasDerivAt_riceMeleNormSq J delta Delta Real.pi).deriv, Real.sin_pi]
  ring

theorem linearGeometricPhase_eq_constantSpeedLift (C : ℤ) (k : ℝ) :
    linearGeometricPhase C k =
      HTGeometry.constantSpeedPhaseLift (2 * Real.pi) (-2 * C)
        (Real.pi * (C : ℝ)) (k + Real.pi) := by
  simp only [linearGeometricPhase, HTGeometry.constantSpeedPhaseLift]
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

theorem paperLinearPhase_minimumAction (C : ℤ) :
    HTGeometry.liftedPhaseAction (2 * Real.pi)
        (HTGeometry.constantSpeedPhaseLift (2 * Real.pi) (-2 * C)
          (Real.pi * (C : ℝ))) =
      2 * Real.pi * (C : ℝ) ^ (2 : ℕ) := by
  rw [HTGeometry.liftedPhaseAction_constantSpeed (by positivity)]
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

def forwardBranchPhase (d gamma : ℝ) : ℝ := d + gamma

def backwardBranchPhase (d gamma : ℝ) : ℝ := d - gamma

theorem commonDynamicalPhase_cancels (d gamma : ℝ) :
    forwardBranchPhase d gamma - backwardBranchPhase d gamma = 2 * gamma := by
  simp [forwardBranchPhase, backwardBranchPhase]
  ring

theorem twoBandCounterScan_cancels_commonMode
    (dClock dSystem gammaClock gammaSystem : ℝ) :
    (forwardBranchPhase dClock gammaClock - backwardBranchPhase dClock gammaClock) -
        (forwardBranchPhase dSystem gammaSystem - backwardBranchPhase dSystem gammaSystem) =
      2 * (gammaClock - gammaSystem) := by
  simp [forwardBranchPhase, backwardBranchPhase]
  ring

def oddCleanGeometricPhase (C : ℤ) (b k : ℝ) : ℝ :=
  linearGeometricPhase C k + b * Real.sin k

theorem oddCleanGeometricPhase_neg (C : ℤ) (b k : ℝ) :
    oddCleanGeometricPhase C b (-k) = -oddCleanGeometricPhase C b k := by
  simp [oddCleanGeometricPhase, linearGeometricPhase, Real.sin_neg]
  ring

def riceMeleDiracMassLoop : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1

theorem riceMeleDiracMassLoop_coordinates (tau : ℝ) :
    riceMeleDiracMassLoop tau =
      ((2 * normalizedPumpDelta tau : ℝ) : ℂ) +
        Complex.I * ((2 * normalizedPumpMass tau : ℝ) : ℂ) := by
  simp [riceMeleDiracMassLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt,
    normalizedPumpDelta, normalizedPumpMass, HTGeometry.referenceRiceMeleDelta,
    HTGeometry.referenceRiceMeleDetuning, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem riceMeleDiracMassLoop_winding :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding riceMeleDiracMassLoop = 1 := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding 1

def paperGeometricLoop (C : ℤ) : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt (-C)

theorem paperGeometricLoop_phase (C : ℤ) (t : ℝ) :
    paperGeometricLoop C t =
      Complex.exp ((linearGeometricPhase C t : ℂ) * Complex.I) := by
  simp [paperGeometricLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt,
    linearGeometricPhase]
  congr 1
  ring

theorem paperGeometricLoop_winding (C : ℤ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (paperGeometricLoop C) = -C := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding (-C)

theorem paperForwardBackwardReadout_winding (C : ℤ) :
    RHTower.windingNumber (fun t => paperGeometricLoop C t ^ (2 : ℕ))
        0 (2 * Real.pi) = -2 * C := by
  rw [RHTower.windingNumber_pow (paperGeometricLoop C).isLoop 2]
  change 2 * PrimeQuasiLocalCharge.scalarCircleLoopWinding (paperGeometricLoop C) = _
  rw [paperGeometricLoop_winding]
  ring

theorem riceMeleDiracReadout_winding :
    RHTower.windingNumber (fun t => paperGeometricLoop 1 t ^ (2 : ℕ))
        0 (2 * Real.pi) = -2 := by
  simpa using paperForwardBackwardReadout_winding 1

def determinantHistoryCircleLoop (N : ℤ) : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt N

theorem determinantHistory_reparameterized (N : ℤ) (t : ℝ) :
    HTGeometry.loopHistory N (t / (2 * Real.pi)) =
      determinantHistoryCircleLoop N t := by
  simp only [HTGeometry.loopHistory, HTGeometry.loopSpeed,
    determinantHistoryCircleLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

theorem determinantHistoryCircleLoop_winding (N : ℤ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (determinantHistoryCircleLoop N) = N := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding N

theorem determinantHistory_clockReadout_winding (N : ℤ) :
    RHTower.windingNumber (fun t => determinantHistoryCircleLoop N t ^ (2 : ℕ))
        0 (2 * Real.pi) = 2 * N := by
  rw [RHTower.windingNumber_pow (determinantHistoryCircleLoop N).isLoop 2]
  change 2 * PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (determinantHistoryCircleLoop N) = 2 * N
  rw [determinantHistoryCircleLoop_winding]

theorem rectangleClockReadout_commonMode_cancel
    {X Y : Type*} (phase : X → Y → ℂ)
    (row : X → ℂ) (column : Y → ℂ)
    (x1 x2 : X) (y1 y2 : Y) :
    HTGeometry.LoopGaugeApplications.rectangleWilsonLoop
        (HTGeometry.exponentialKernel
          (fun x y => row x + phase x y + column y))
        x1 x2 y1 y2 =
      HTGeometry.LoopGaugeApplications.rectangleWilsonLoop
        (HTGeometry.exponentialKernel phase)
        x1 x2 y1 y2 := by
  exact HTGeometry.LoopGaugeApplications.rectangleWilsonLoop_separableGauge
    phase row column x1 x2 y1 y2

theorem reflectedScaleClockHolonomy_invariant (epsilon : ℕ → ℝ) (N : ℕ) :
    HTGeometry.scaleInnovationGaugeHolonomy
        (HTGeometry.scaleInnovationGaugeGlobalReflect epsilon) N =
      HTGeometry.scaleInnovationGaugeHolonomy epsilon N := by
  exact HTGeometry.scaleInnovationGaugeHolonomy_globalReflect epsilon N

theorem toricClockReadout_doubling_vanishes
    (a b : Quantum.Stabilizer.Lattice.toricH1 (L := 2)) :
    2 * Quantum.Stabilizer.Lattice.toricChernSimonsLinking a b = 0 := by
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

theorem toricFundamentalClockReadout_vanishes :
    2 * Quantum.Stabilizer.Lattice.toricChernSimonsLinking
        Quantum.Stabilizer.Lattice.toricHorizontalWilsonLoop
        Quantum.Stabilizer.Lattice.toricVerticalWilsonLoop = 0 := by
  exact toricClockReadout_doubling_vanishes _ _

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
