import GaloisForLFunctions.HTGeometry.CyclicGaugeAttainmentWallCrossing
import GaloisForLFunctions.HTGeometry.SourceFaceDifferentialAlgebraicInertiaUniversalityLaw

/-!
# Cyclic differentially-algebraic gauge wall attainment

The positive Gamma Fourier modes in source-face gauge inertia are exactly the normalized gauges of
the shrinking cyclic wall. Consequently arbitrary finite wall packets remain differentially
algebraic even while the wall periods and incidence symbols vanish and the first gauge jets escape
to infinity.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite packet in the initial cyclic-wall gauges. -/
def cyclicWallGaugePacket {k : ℕ} (a : Fin k → ℂ) (z : ℂ) : ℂ :=
  ∑ m : Fin k, a m * cyclicWallGauge m z

/-- Cyclic-wall packets are exactly the positive Gamma Fourier packets. -/
theorem cyclicWallGaugePacket_eq_gammaPositivePeriodicFourierPacket
    {k : ℕ} (a : Fin k → ℂ) :
    cyclicWallGaugePacket a = gammaPositivePeriodicFourierPacket a := by
  funext z
  simp [cyclicWallGaugePacket, gammaPositivePeriodicFourierPacket, cyclicWallGauge]

/-- Every gauge along the shrinking cyclic wall is differentially algebraic. -/
theorem differentiallyAlgebraic_cyclicWallGauge (n : ℕ) :
    DifferentiallyAlgebraic (cyclicWallGauge n) := by
  simpa [cyclicWallGauge, gammaPeriodicMode] using
    differentiallyAlgebraic_cexp_linear (gammaPeriodicFrequency (n + 1))

/-- Every finite wall slice is an independent DA packet phase, destroyed by any nonreal
translation removed at the source face. -/
theorem nonreal_cyclicWall_arbitraryDifferentialAlgebraicGaugeBirth
    (tau : ℂ) (htau : tau.im ≠ 0) (k : ℕ) :
    LinearIndependent ℂ (fun m : Fin k => cyclicWallGauge m) ∧
      ∀ a : Fin k → ℂ,
        DifferentiallyAlgebraic (cyclicWallGaugePacket a) ∧
        Function.Periodic (cyclicWallGaugePacket a) 1 ∧
        (a ≠ 0 → ¬ Function.Periodic (cyclicWallGaugePacket a) tau) := by
  simpa [cyclicWallGaugePacket, cyclicWallGauge,
    gammaPositivePeriodicFourierPacket] using
    nonreal_sourceFace_arbitraryDifferentialAlgebraicGaugeBirth tau htau k

/-- **Cyclic DA-gauge wall-attainment universality.** Arbitrary-rank source-face gauge birth,
shrinking-period wall crossing, divergent first jets, vanishing incidence, and exact
gauge/attainment conservation all occur inside the differentially algebraic gauge sector. -/
theorem cyclicWall_differentialAlgebraicAttainmentUniversality
    (tau : ℂ) (htau : tau.im ≠ 0) (k : ℕ) :
    (LinearIndependent ℂ (fun m : Fin k => cyclicWallGauge m) ∧
      ∀ a : Fin k → ℂ,
        DifferentiallyAlgebraic (cyclicWallGaugePacket a) ∧
        Function.Periodic (cyclicWallGaugePacket a) 1 ∧
        (a ≠ 0 → ¬ Function.Periodic (cyclicWallGaugePacket a) tau)) ∧
    (∀ n : ℕ,
      DifferentiallyAlgebraic (cyclicWallGauge n) ∧
      Function.Periodic (cyclicWallGauge n) (cyclicWallPeriod n) ∧
      ‖GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n)‖⁻¹ =
        1 + ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖ / (2 * Real.pi)) ∧
    Tendsto cyclicWallPeriod atTop (𝓝 0) ∧
    Tendsto (fun n ↦ ‖iteratedDeriv 1 (cyclicWallGauge n) 0‖) atTop atTop ∧
    Tendsto
      (fun n ↦ ‖GaloisForLFunctions.regularizedPeriodWeight (cyclicWallPeriod n)‖)
      atTop (𝓝 0) := by
  refine ⟨nonreal_cyclicWall_arbitraryDifferentialAlgebraicGaugeBirth tau htau k,
    ?_, cyclicWallPeriod_tendsto_zero, cyclicWallGauge_firstJet_tendsto_atTop,
    norm_cyclicWallIncidenceWeight_tendsto_zero⟩
  intro n
  exact ⟨differentiallyAlgebraic_cyclicWallGauge n,
    cyclicWallGauge_periodic n, cyclicWall_gaugeAttainment_conservation n⟩

end

end GaloisForLFunctions.HTGeometry
