import GaloisForLFunctions.RHTower.RiceMeleTopologicalClockApplications
import GaloisForLFunctions.HTGeometry.MarkedHalfCharacterCompactActionLaw
import GaloisForLFunctions.HTGeometry.LoopGaugeApplications
import GaloisForLFunctions.HTGeometry.ScaleInnovationPhaseGauge
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.AbelianChernSimons

/-!
# Topological clock bridges: Rice-Mele, winding readouts and gauge cancellations

This module collects exact identities connecting the topological clock applications to existing
corpus objects. For the Rice-Mele Bloch vector with `|d(k)|^2 = Δ^2 + 2J^2(1 + δ^2 + (1 - δ^2) cos k)`
it evaluates the values at `k = 0, π`, the derivative in `k`, and the zone-edge minimality on the
normalized pump loop. It identifies the linear geometric phase `-C k` with a constant-speed phase
lift of action `2πC^2`, computes windings of circle loops and of their squared (forward-backward)
readouts, and records common-mode cancellations: forward minus backward branch phases, separable
gauges in rectangle Wilson loops, global reflection of scale gauges, and the vanishing of doubled
`Z/2` toric Chern-Simons linking.

## Main results

- `riceMeleNormSq_zero`, `riceMeleNormSq_pi`: `|d(0)|^2 = Δ^2 + 4J^2` and `|d(π)|^2 = Δ^2 + 4J^2 δ^2`.
- `normalizedPump_zoneEdge_minimal`: on the normalized pump loop, `|d(k)|^2` is minimal at `k = π`.
- `hasDerivAt_riceMeleNormSq`: `d/dk |d(k)|^2 = -2J^2(1 - δ^2) sin k`.
- `paperLinearPhase_minimumAction`: the constant-speed lift of `-C k` has action `2πC^2` on `[0, 2π]`.
- `paperForwardBackwardReadout_winding`: the squared geometric loop of Chern number `C` winds
  `-2C` times.
- `determinantHistory_clockReadout_winding`: the squared determinant-history loop winds `2N` times.
- `rectangleClockReadout_commonMode_cancel`: separable row and column phases cancel from rectangle
  Wilson loops.
- `toricFundamentalClockReadout_vanishes`: twice the toric Chern-Simons linking of the fundamental
  Wilson loops vanishes in `Z/2`.

## Hypotheses

All results are unconditional identities.
-/

open scoped BigOperators Matrix
open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower.TopologicalClockApplications

/-- At `k = 0` the Rice-Mele Bloch norm is `|d(0)|^2 = Δ^2 + 4J^2`. -/
theorem riceMeleNormSq_zero (J delta Delta : ℝ) :
    riceMeleNormSq J delta Delta 0 = Delta ^ (2 : ℕ) + 4 * J ^ (2 : ℕ) := by
  rw [riceMeleNormSq_eq]
  simp
  ring

/-- At the zone edge `k = π` the Rice-Mele Bloch norm is `|d(π)|^2 = Δ^2 + 4J^2 δ^2`. -/
theorem riceMeleNormSq_pi (J delta Delta : ℝ) :
    riceMeleNormSq J delta Delta Real.pi = Delta ^ (2 : ℕ) + 4 * J ^ (2 : ℕ) * delta ^ (2 : ℕ) := by
  rw [riceMeleNormSq_eq, Real.cos_pi]
  ring

/-- On the normalized pump loop (`J = 1`, pump parameters at time `τ`), `|d(π)|^2 ≤ |d(k)|^2` for
every quasimomentum `k`. -/
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

/-- The Rice-Mele Bloch norm has `k`-derivative `-2J^2(1 - δ^2) sin k`. -/
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

/-- `k = 0` is a stationary point of the Rice-Mele Bloch norm. -/
theorem riceMeleNormSq_stationary_zero (J delta Delta : ℝ) :
    deriv (fun q => riceMeleNormSq J delta Delta q) 0 = 0 := by
  rw [(hasDerivAt_riceMeleNormSq J delta Delta 0).deriv]
  simp

/-- `k = π` is a stationary point of the Rice-Mele Bloch norm. -/
theorem riceMeleNormSq_stationary_pi (J delta Delta : ℝ) :
    deriv (fun q => riceMeleNormSq J delta Delta q) Real.pi = 0 := by
  rw [(hasDerivAt_riceMeleNormSq J delta Delta Real.pi).deriv, Real.sin_pi]
  ring

/-- The linear geometric phase `-C k` is the constant-speed phase lift on `[0, 2π]` with winding
parameter `-2C` and initial phase `πC`, evaluated at `k + π`. -/
theorem linearGeometricPhase_eq_constantSpeedLift (C : ℤ) (k : ℝ) :
    linearGeometricPhase C k =
      HTGeometry.constantSpeedPhaseLift (2 * Real.pi) (-2 * C)
        (Real.pi * (C : ℝ)) (k + Real.pi) := by
  simp only [linearGeometricPhase, HTGeometry.constantSpeedPhaseLift]
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

/-- The constant-speed lift of the linear geometric phase has kinetic action `2πC^2` on `[0, 2π]`. -/
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

/-- The difference of forward phase `d + γ` and backward phase `d - γ` is `2γ`: the dynamical phase
cancels. -/
theorem commonDynamicalPhase_cancels (d gamma : ℝ) :
    forwardBranchPhase d gamma - backwardBranchPhase d gamma = 2 * gamma := by
  simp [forwardBranchPhase, backwardBranchPhase]
  ring

/-- In a two-band counter scan, the difference of clock and system forward-backward readouts is
`2(γ_clock - γ_system)`, independent of the dynamical phases. -/
theorem twoBandCounterScan_cancels_commonMode
    (dClock dSystem gammaClock gammaSystem : ℝ) :
    (forwardBranchPhase dClock gammaClock - backwardBranchPhase dClock gammaClock) -
        (forwardBranchPhase dSystem gammaSystem - backwardBranchPhase dSystem gammaSystem) =
      2 * (gammaClock - gammaSystem) := by
  simp [forwardBranchPhase, backwardBranchPhase]
  ring

/-- The geometric phase `-C k + b sin k`: linear Chern part plus an odd sine correction. -/
def oddCleanGeometricPhase (C : ℤ) (b k : ℝ) : ℝ :=
  linearGeometricPhase C k + b * Real.sin k

/-- The phase `-C k + b sin k` is odd in `k`. -/
theorem oddCleanGeometricPhase_neg (C : ℤ) (b k : ℝ) :
    oddCleanGeometricPhase C b (-k) = -oddCleanGeometricPhase C b k := by
  simp [oddCleanGeometricPhase, linearGeometricPhase, Real.sin_neg]
  ring

/-- The Rice-Mele Dirac-mass loop: the unit circle loop of winding one. -/
def riceMeleDiracMassLoop : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt 1

/-- The Dirac-mass loop at time `τ` has coordinates `2δ(τ) + 2i m(τ)` in the normalized pump
parameters. -/
theorem riceMeleDiracMassLoop_coordinates (tau : ℝ) :
    riceMeleDiracMassLoop tau =
      ((2 * normalizedPumpDelta tau : ℝ) : ℂ) +
        Complex.I * ((2 * normalizedPumpMass tau : ℝ) : ℂ) := by
  simp [riceMeleDiracMassLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt,
    normalizedPumpDelta, normalizedPumpMass, HTGeometry.referenceRiceMeleDelta,
    HTGeometry.referenceRiceMeleDetuning, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

/-- The Dirac-mass loop has winding number `1`. -/
theorem riceMeleDiracMassLoop_winding :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding riceMeleDiracMassLoop = 1 := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding 1

/-- The geometric-phase circle loop of Chern number `C`, of winding `-C`. -/
def paperGeometricLoop (C : ℤ) : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt (-C)

/-- The geometric loop is `t ↦ exp(i (-C t))`. -/
theorem paperGeometricLoop_phase (C : ℤ) (t : ℝ) :
    paperGeometricLoop C t =
      Complex.exp ((linearGeometricPhase C t : ℂ) * Complex.I) := by
  simp [paperGeometricLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt,
    linearGeometricPhase]
  congr 1
  ring

/-- The geometric loop of Chern number `C` has winding number `-C`. -/
theorem paperGeometricLoop_winding (C : ℤ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (paperGeometricLoop C) = -C := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding (-C)

/-- The squared geometric loop, the forward-backward readout, has winding number `-2C` over
`[0, 2π]`. -/
theorem paperForwardBackwardReadout_winding (C : ℤ) :
    RHTower.windingNumber (fun t => paperGeometricLoop C t ^ (2 : ℕ))
        0 (2 * Real.pi) = -2 * C := by
  rw [RHTower.windingNumber_pow (paperGeometricLoop C).isLoop 2]
  change 2 * PrimeQuasiLocalCharge.scalarCircleLoopWinding (paperGeometricLoop C) = _
  rw [paperGeometricLoop_winding]
  ring

/-- For Chern number `1`, the forward-backward readout winds `-2` times. -/
theorem riceMeleDiracReadout_winding :
    RHTower.windingNumber (fun t => paperGeometricLoop 1 t ^ (2 : ℕ))
        0 (2 * Real.pi) = -2 := by
  simpa using paperForwardBackwardReadout_winding 1

/-- The determinant-history circle loop of winding `N`. -/
def determinantHistoryCircleLoop (N : ℤ) : PrimeQuasiLocalCharge.ScalarCircleLoop :=
  PrimeQuasiLocalCharge.scalarCircleLoopOfInt N

/-- The unit-interval loop history of winding `N`, reparameterized by `t / (2π)`, is the
determinant-history circle loop. -/
theorem determinantHistory_reparameterized (N : ℤ) (t : ℝ) :
    HTGeometry.loopHistory N (t / (2 * Real.pi)) =
      determinantHistoryCircleLoop N t := by
  simp only [HTGeometry.loopHistory, HTGeometry.loopSpeed,
    determinantHistoryCircleLoop, PrimeQuasiLocalCharge.scalarCircleLoopOfInt]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The determinant-history circle loop has winding number `N`. -/
theorem determinantHistoryCircleLoop_winding (N : ℤ) :
    PrimeQuasiLocalCharge.scalarCircleLoopWinding (determinantHistoryCircleLoop N) = N := by
  exact PrimeQuasiLocalCharge.scalarCircleLoopOfInt_winding N

/-- The squared determinant-history loop has winding number `2N` over `[0, 2π]`. -/
theorem determinantHistory_clockReadout_winding (N : ℤ) :
    RHTower.windingNumber (fun t => determinantHistoryCircleLoop N t ^ (2 : ℕ))
        0 (2 * Real.pi) = 2 * N := by
  rw [RHTower.windingNumber_pow (determinantHistoryCircleLoop N).isLoop 2]
  change 2 * PrimeQuasiLocalCharge.scalarCircleLoopWinding
      (determinantHistoryCircleLoop N) = 2 * N
  rw [determinantHistoryCircleLoop_winding]

/-- Separable gauge invariance: adding row and column phases `r(x) + c(y)` to the phase kernel does
not change the rectangle Wilson loop of its exponential. -/
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

/-- Globally reflecting every scale phase leaves the adjacent holonomy `ε(N+1) ε(N)` unchanged. -/
theorem reflectedScaleClockHolonomy_invariant (epsilon : ℕ → ℝ) (N : ℕ) :
    HTGeometry.scaleInnovationGaugeHolonomy
        (HTGeometry.scaleInnovationGaugeGlobalReflect epsilon) N =
      HTGeometry.scaleInnovationGaugeHolonomy epsilon N := by
  exact HTGeometry.scaleInnovationGaugeHolonomy_globalReflect epsilon N

/-- On the `L = 2` toric code, twice the `Z/2` Chern-Simons linking of any two homology classes is
zero. -/
theorem toricClockReadout_doubling_vanishes
    (a b : Quantum.Stabilizer.Lattice.toricH1 (L := 2)) :
    2 * Quantum.Stabilizer.Lattice.toricChernSimonsLinking a b = 0 := by
  rw [show (2 : ZMod 2) = 0 from ZMod.natCast_self 2, zero_mul]

/-- Twice the `Z/2` linking of the horizontal and vertical toric Wilson loops vanishes. -/
theorem toricFundamentalClockReadout_vanishes :
    2 * Quantum.Stabilizer.Lattice.toricChernSimonsLinking
        Quantum.Stabilizer.Lattice.toricHorizontalWilsonLoop
        Quantum.Stabilizer.Lattice.toricVerticalWilsonLoop = 0 := by
  exact toricClockReadout_doubling_vanishes _ _

end GaloisForLFunctions.RHTower.TopologicalClockApplications

end
