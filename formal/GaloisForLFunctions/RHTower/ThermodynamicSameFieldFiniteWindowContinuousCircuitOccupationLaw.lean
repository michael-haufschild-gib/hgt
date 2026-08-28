import GaloisForLFunctions.HTGeometry.FiniteWindowContinuousCircuitOccupationLaw
import GaloisForLFunctions.RHTower.ThermodynamicSameFieldContinuousCircuitOccupationLaw

/-!
# One-field finite-window continuous-circuit occupation law

The same absolutely summable static nearest-neighbour qubit field that carries the thermodynamic
recurrence lifecycle has a quantitative continuous-circuit occupation bound on every literal
prefix and every finite translated laboratory window.  Its finite-time correction is controlled by
the minimum of a finite list of spectroscopic detunings.
-/

open Filter MeasureTheory Set Topology Matrix
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Explicit upper envelope for one literal prefix, Fejer resolution, and laboratory duration. -/
noncomputable def thermodynamicLiteralPrefixFiniteWindowCircuitOccupationBound
    (p : InfinitePathLabel → ℝ) (k N : ℕ) (T : ℝ) : ℝ :=
  let n := k + 3
  let d := thermodynamicLiteralPrefixProjectiveDimension k
  let energy := thermodynamicLiteralPrefixCanonicalEnergy p k
  let rho := finiteWindowContinuousCircuitCubeRadius
  (2 : ℝ) ^ d * T *
    atMostTwentiethCircuitEntropyBound n (nearHilbertContinuousCircuitBudget n) *
      ((2 * rho / (2 * Real.pi) + periodicTentFejerError N (2 * rho)) ^ d +
        ((nonconstantPacketIndexSet N d).card : ℝ) *
          ((((N : ℝ) + 1)⁻¹ *
            (2 * rho / (2 * Real.pi) + periodicTentFejerError N (2 * rho))) ^ d) *
          (2 / (T * finitePacketDetuningFloor N
            (zeroProjectiveFrequency energy))))

/-- The finite packet detuning used by the laboratory-window law is strictly positive at every
literal prefix and every Fejer resolution. -/
theorem ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_finitePacketDetuningFloor_pos
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p)
    (k N : ℕ) :
    0 < finitePacketDetuningFloor N
      (zeroProjectiveFrequency (thermodynamicLiteralPrefixCanonicalEnergy p k)) := by
  apply finitePacketDetuningFloor_pos
  exact maximallyProjectiveEnergy_zeroProjectiveFrequency_independent _
    (maximallyProjectiveEnergy_thermodynamicLiteralPrefixCanonicalEnergy hp k)

/-- Every translated finite laboratory window obeys the explicit circuit-occupation envelope. -/
theorem ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitFiniteWindow
    {p : InfinitePathLabel → ℝ} (hp : ThermodynamicSameFieldLifecycle p)
    (k N : ℕ) (u T : ℝ) (hT : 0 < T) :
    (volume
      (projectiveContinuousCircuitCaptureTimes
          (thermodynamicLiteralPrefixCanonicalEnergy p k)
          (thermodynamicLiteralPrefixConfigEquiv k)
          (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
          (nearHilbertContinuousCircuitBudget (k + 3)) ∩
        Set.Ioc u (u + T))).toReal ≤
      thermodynamicLiteralPrefixFiniteWindowCircuitOccupationBound p k N T := by
  simpa [thermodynamicLiteralPrefixFiniteWindowCircuitOccupationBound] using
    maximallyProjective_continuousCircuitCapture_finiteWindow_le
      (thermodynamicLiteralPrefixCanonicalEnergy p k)
      (maximallyProjectiveEnergy_thermodynamicLiteralPrefixCanonicalEnergy hp k)
      (thermodynamicLiteralPrefixConfigEquiv k)
      (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
      (s := nearHilbertContinuousCircuitBudget (k + 3)) N u T hT

/-- Membership in the finite-window event is exactly physical operator-norm approximation, modulo
global phase, by a circuit at the stated gate budget. -/
theorem thermodynamicLiteralPrefixContinuousCircuitCaptureTimes_physical_iff
    (p : InfinitePathLabel → ℝ) (k : ℕ) (t : ℝ) :
    t ∈ projectiveContinuousCircuitCaptureTimes
          (thermodynamicLiteralPrefixCanonicalEnergy p k)
          (thermodynamicLiteralPrefixConfigEquiv k)
          (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
          (nearHilbertContinuousCircuitBudget (k + 3)) ↔
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (k + 3),
        C.gateCount ≤ nearHilbertContinuousCircuitBudget (k + 3) ∧
        ‖unitaryEvolution (pathHamiltonian (infinitePathPrefixShell k p)) t -
          c • (C.eval : Matrix (Fin (k + 3) → Bool)
            (Fin (k + 3) → Bool) ℂ)‖ ≤ (1 / 20 : ℝ) := by
  exact thermodynamicLiteralPrefixContinuousCircuitCaptureTarget_physical_iff p k t

/-- One static local field simultaneously carries the recurrence-desert lifecycle and every
finite-window continuous-circuit occupation law. -/
theorem exists_thermodynamicSameFieldFiniteWindowContinuousCircuitOccupationLaw :
    ∃ p : InfinitePathLabel → ℝ,
      ThermodynamicRecurrenceDesertLifecycle p ∧
      ∀ k N : ℕ, ∀ u T : ℝ, 0 < T →
        0 < finitePacketDetuningFloor N
          (zeroProjectiveFrequency (thermodynamicLiteralPrefixCanonicalEnergy p k)) ∧
        (volume
          (projectiveContinuousCircuitCaptureTimes
              (thermodynamicLiteralPrefixCanonicalEnergy p k)
              (thermodynamicLiteralPrefixConfigEquiv k)
              (thermodynamicLiteralPrefixCanonicalEigenbasisUnitary p k)
              (nearHilbertContinuousCircuitBudget (k + 3)) ∩
            Set.Ioc u (u + T))).toReal ≤
          thermodynamicLiteralPrefixFiniteWindowCircuitOccupationBound p k N T := by
  obtain ⟨p, hp⟩ := exists_thermodynamicRecurrenceDesertLifecycle
  refine ⟨p, hp, ?_⟩
  intro k N u T hT
  exact ⟨
    ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_finitePacketDetuningFloor_pos
        hp.toThermodynamicSameFieldLifecycle k N,
    ThermodynamicSameFieldLifecycle.thermodynamicLiteralPrefix_continuousCircuitFiniteWindow
        hp.toThermodynamicSameFieldLifecycle k N u T hT⟩

end

end RHTower
