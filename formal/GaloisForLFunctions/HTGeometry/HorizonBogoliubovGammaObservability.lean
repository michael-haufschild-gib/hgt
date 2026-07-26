import GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary
import GaloisForLFunctions.HTGeometry.GammaReflectionRatioClock
import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Horizon Bogoliubov Gamma observability

For the Carlitz--Willey moving mirror, the exact Bogoliubov coefficient has a Gamma core
`Gamma(i*omega/kappa)`; see Good--Anderson--Evans, *Time Dependence of Particle Creation from
Accelerating Mirrors*, arXiv:1303.6756, Table IV.  Gianfelici--Mancini,
*Quantum channels from reflections on moving mirrors*, arXiv:1704.04635, additionally display
the resulting `arg Gamma(i*omega/kappa)` contribution to the quantum-channel phase.

Use the dimensionless complex-frequency coordinate `z=i*omega/kappa`.  The conjugate-frequency
intensity core is then `Gamma(z)*Gamma(-z)`, while the oriented phase quotient is
`Gamma(z)/Gamma(-z)`.  Euler reflection makes the first differentially algebraic.  The second is
unconditionally hypertranscendental.

The capstone is an observability separation: no scalar-aware finite differential circuit can
recover the phase quotient from the intensity core.  The HT datum therefore resides in the
orientation-sensitive observation structure, even though an intensity-only readout is DA.  This
is not a claim that the mirror trajectory or physical time evolution is hypertranscendental.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Gamma core of a thermal-horizon Bogoliubov amplitude in the complex-frequency coordinate
`z=i*omega/kappa`. -/
def horizonBogoliubovGammaAmplitudeMero : meroField Set.univ :=
  gammaShiftMero 0

/-- The opposite-frequency Gamma core.  On the physical imaginary-frequency line this is the
complex conjugate of the amplitude core. -/
def horizonBogoliubovGammaConjugateFrequencyMero : meroField Set.univ :=
  gammaNegativeShiftMero 0

/-- Intensity-only Gamma core obtained by multiplying the two frequency orientations. -/
def horizonBogoliubovGammaIntensityCoreMero : meroField Set.univ :=
  horizonBogoliubovGammaAmplitudeMero *
    horizonBogoliubovGammaConjugateFrequencyMero

/-- Orientation-sensitive phase quotient. -/
def horizonBogoliubovGammaPhaseQuotientMero : meroField Set.univ :=
  (gammaReflectionRatioMero 0)⁻¹

/-- Wigner--Smith/logarithmic delay of the positive-frequency horizon Gamma amplitude. -/
def horizonBogoliubovGammaWignerSmithLogClockMero : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock horizonBogoliubovGammaAmplitudeMero

/-- The horizon Wigner--Smith observable is exactly the zero-shift meromorphic digamma clock. -/
theorem horizonBogoliubovGammaWignerSmithLogClockMero_eq_digamma :
    horizonBogoliubovGammaWignerSmithLogClockMero = digammaShiftMero 0 := by
  rfl

theorem horizonBogoliubovGammaConjugateFrequencyMero_ne_zero :
    horizonBogoliubovGammaConjugateFrequencyMero ≠ 0 := by
  rw [horizonBogoliubovGammaConjugateFrequencyMero,
    gammaNegativeShiftMero_reflection]
  exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero 0)
    (inv_ne_zero (gammaShiftMero_ne_zero (1 - 0)))

/-- The horizon intensity is exactly the zero-shift opposite-orientation Gamma product. -/
theorem horizonBogoliubovGammaIntensityCoreMero_eq_oppositeProduct :
    horizonBogoliubovGammaIntensityCoreMero =
      gammaOppositeShiftProductMero 0 0 := rfl

/-- **Horizon reflection value relation.**  The conjugate-frequency product is a sine gauge times
the adjacent Gamma ratio `Gamma(z)/Gamma(z+1)`. -/
theorem horizonBogoliubovGammaIntensityCoreMero_reflection :
    horizonBogoliubovGammaIntensityCoreMero =
      gammaReflectionGaugeMero 0 *
        reducedVenezianoAmplitudeMero 0 1 := by
  rw [horizonBogoliubovGammaIntensityCoreMero_eq_oppositeProduct,
    gammaOppositeShiftProductMero_eq_gauge_mul_reducedVeneziano]
  norm_num

/-- The Gamma intensity core is DA: conjugate-frequency multiplication closes the two oriented
Gamma contributions onto one integer-translation orbit. -/
theorem differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero :
    DifferentialAlgebraicOver (RatFunc ℂ)
      horizonBogoliubovGammaIntensityCoreMero := by
  rw [horizonBogoliubovGammaIntensityCoreMero_eq_oppositeProduct,
    differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSum]
  exact ⟨0, by norm_num⟩

/-- The chosen reflection-clock presentation is the physical orientation quotient
`Gamma(z)/Gamma(-z)`. -/
theorem horizonBogoliubovGammaPhaseQuotientMero_eq_ratio :
    horizonBogoliubovGammaPhaseQuotientMero =
      horizonBogoliubovGammaAmplitudeMero /
        horizonBogoliubovGammaConjugateFrequencyMero := by
  simp [horizonBogoliubovGammaPhaseQuotientMero,
    gammaReflectionRatioMero, horizonBogoliubovGammaAmplitudeMero,
    horizonBogoliubovGammaConjugateFrequencyMero]

/-- The orientation-sensitive horizon phase remains HT even though its intensity core is DA. -/
theorem hypertranscendentalOver_horizonBogoliubovGammaPhaseQuotientMero :
    HypertranscendentalOver (RatFunc ℂ)
      horizonBogoliubovGammaPhaseQuotientMero := by
  rw [horizonBogoliubovGammaPhaseQuotientMero,
    HTGeometry.hypertranscendentalOver_inv_iff]
  exact hypertranscendentalOver_gammaReflectionRatioMero 0

/-- **Positive horizon delay source.**  The directly observable logarithmic scattering delay is
HT even though the conjugate-frequency intensity core is DA. -/
theorem hypertranscendentalOver_horizonBogoliubovGammaWignerSmithLogClockMero :
    HypertranscendentalOver (RatFunc ℂ)
      horizonBogoliubovGammaWignerSmithLogClockMero := by
  rw [horizonBogoliubovGammaWignerSmithLogClockMero_eq_digamma]
  let b : Fin 1 → ℂ := fun _ => 0
  let M : Fin 1 → ℂ := fun _ => 1
  have h := hypertranscendentalOver_gammaOrbitDigammaMero b M 0
    (by simp [M])
    (by
      intro c hc
      exact (hc (Subsingleton.elim c 0)).elim)
  simpa [b, M, gammaOrbitDigammaMero] using h

/-- No DA multiplicative phase calibration transforms the opposite-frequency Gamma carrier into
the positive-frequency carrier. -/
theorem horizonBogoliubovGammaAmplitudeMero_ne_da_mul_conjugate
    (g : meroField Set.univ)
    (hg : DifferentialAlgebraicOver (RatFunc ℂ) g) :
    horizonBogoliubovGammaAmplitudeMero ≠
      g * horizonBogoliubovGammaConjugateFrequencyMero := by
  intro heq
  apply hypertranscendentalOver_horizonBogoliubovGammaPhaseQuotientMero
  have hphase : horizonBogoliubovGammaPhaseQuotientMero = g := by
    rw [horizonBogoliubovGammaPhaseQuotientMero_eq_ratio, heq]
    exact mul_div_cancel_right₀ g
      horizonBogoliubovGammaConjugateFrequencyMero_ne_zero
  rw [hphase]
  exact hg

/-- **Finite-observation non-recovery.**  Base rational clocks and the complete intensity core,
closed under finitely many field operations and differentiations, cannot reconstruct the horizon
phase quotient.  A phase-sensitive realization therefore needs an HT non-intensity source. -/
theorem no_scalarAwareFiniteDifferentialCircuit_horizonPhase_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = horizonBogoliubovGammaIntensityCoreMero))
      horizonBogoliubovGammaPhaseQuotientMero := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      hypertranscendentalOver_horizonBogoliubovGammaPhaseQuotientMero hcircuit
  rw [ha] at hHT
  exact hHT differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero

/-- Rational clocks and the complete DA horizon intensity cannot finitely reconstruct the HT
Wigner--Smith/digamma delay. -/
theorem no_scalarAwareFiniteDifferentialCircuit_horizonWignerSmith_from_intensity :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a => a = horizonBogoliubovGammaIntensityCoreMero))
      horizonBogoliubovGammaWignerSmithLogClockMero := by
  exact HTGeometry.no_scalarAwareFiniteDifferentialCircuit_wignerSmith_from_daObservation
    horizonBogoliubovGammaAmplitudeMero
    horizonBogoliubovGammaIntensityCoreMero
    (by
      rw [horizonBogoliubovGammaAmplitudeMero]
      let b : Fin 1 → ℂ := fun _ => 0
      let m : Fin 1 → ℤ := fun _ => 1
      have h := hypertranscendentalOver_gammaOrbitProductMero b m 0
        (by simp [m])
        (by
          intro c hc
          exact (hc (Subsingleton.elim c 0)).elim)
      simpa [b, m, gammaOrbitProductMero] using h)
    differentialAlgebraicOver_horizonBogoliubovGammaIntensityCoreMero

end

end GaloisForLFunctions
