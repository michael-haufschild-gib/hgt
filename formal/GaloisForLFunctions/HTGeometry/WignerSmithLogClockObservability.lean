import GaloisForLFunctions.HTGeometry.GammaReflectedFrequencyObservability
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Wigner--Smith logarithmic clock observability

For a scalar scattering channel with nonzero scattering element `S`, the Wigner--Smith time-delay
observable is, up to the conventional nonzero constant and the chosen frequency calibration,

`S' / S`.

This module treats that logarithmic derivative as an observation of the scattering clock.  The
existing source-logarithmic boundary gives an exact theorem: the Wigner--Smith logarithmic clock is
hypertranscendental if and only if the scattering element is.  Hence differentiating the phase does
not collapse the HT source.

For opposite-orientation Gamma scattering clocks, the delay is exactly the difference of the two
oriented Gamma logarithmic derivatives.  When the two shifts differ by a nonnegative integer, the
reflected-frequency intensity is DA but the delay remains HT and cannot be reconstructed by a
finite differential circuit from intensity and rational clocks.

Physics provenance for the observation map: U. R. Patel and E. Michielssen,
*Wigner--Smith Time Delay Matrix for Electromagnetics: Theory and Phenomenology*, arXiv:2003.06985.
The same derivative-of-scattering-matrix relation is standard in quantum and acoustic scattering.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

namespace HTGeometry

noncomputable section

/-- Algebraic logarithmic current underlying the scalar Wigner--Smith delay.  Physical conventions
multiply this by a nonzero constant such as `-i` and by the frequency-coordinate scale. -/
def wignerSmithLogClock
    {L : Type*} [Field L] [Differential L] (S : L) : L :=
  Differential.logDeriv S

/-- **Exact Wigner--Smith differential boundary.**  The logarithmic time-delay clock is HT exactly
when the scalar scattering clock is HT. -/
theorem hypertranscendentalOver_wignerSmithLogClock_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L] (S : L) :
    HypertranscendentalOver K (wignerSmithLogClock S) ↔
      HypertranscendentalOver K S := by
  simpa [wignerSmithLogClock, Differential.logDeriv] using
    (hypertranscendentalOver_deriv_div_self_iff (K := K) S)

/-- A DA observation channel cannot finitely generate the Wigner--Smith clock of an HT scattering
element.  Thus a trivial or DA intensity does not imply a finite phase-delay observation. -/
theorem no_scalarAwareFiniteDifferentialCircuit_wignerSmith_from_daObservation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DifferentialAlgebra K L]
    [CharZero K] [CharZero L]
    (S observation : L) (hS : HypertranscendentalOver K S)
    (hObservation : DifferentialAlgebraicOver K observation) :
    ¬ FiniteDifferentialCircuit
      (BaseScalarOrAtom K L (fun a => a = observation))
      (wignerSmithLogClock S) := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      ((hypertranscendentalOver_wignerSmithLogClock_iff S).2 hS) hcircuit
  rw [ha] at hHT
  exact hHT hObservation

end

end HTGeometry

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Logarithmic derivative of a negative-orientation Gamma factor. -/
def gammaNegativeLogDerivativeMero (b : ℂ) : meroField Set.univ :=
  Differential.logDeriv (gammaNegativeShiftMero b)

/-- Wigner--Smith logarithmic clock of an opposite-orientation Gamma scattering element. -/
def gammaOppositeShiftWignerSmithLogMero (a b : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock (gammaOppositeShiftQuotientMero a b)

/-- **Gamma Wigner--Smith value relation.**  The delay current is exactly the positive-orientation
digamma clock minus the logarithmic derivative of the negative-orientation Gamma factor. -/
theorem gammaOppositeShiftWignerSmithLogMero_eq_orientedLogDerivatives
    (a b : ℂ) :
    gammaOppositeShiftWignerSmithLogMero a b =
      digammaShiftMero a - gammaNegativeLogDerivativeMero b := by
  unfold gammaOppositeShiftWignerSmithLogMero HTGeometry.wignerSmithLogClock
  unfold gammaOppositeShiftQuotientMero
  rw [Differential.logDeriv_div]
  · rfl
  · exact gammaShiftMero_ne_zero a
  · rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero b)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - b)))

/-- Every opposite-orientation Gamma scattering clock has an HT Wigner--Smith logarithmic delay. -/
theorem hypertranscendentalOver_gammaOppositeShiftWignerSmithLogMero
    (a b : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gammaOppositeShiftWignerSmithLogMero a b) := by
  rw [gammaOppositeShiftWignerSmithLogMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff]
  exact hypertranscendentalOver_gammaOppositeShiftQuotientMero a b

/-- **Delay survives intensity collapse.**  At every nonnegative integer shift separation, the
Gamma intensity is DA but no scalar-aware finite differential circuit built from that intensity
and rational clocks reconstructs the HT Wigner--Smith delay. -/
theorem no_scalarAwareFiniteDifferentialCircuit_gammaWignerSmith_from_integerShiftIntensity
    (a : ℂ) (n : ℕ) :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun x => x = gammaOppositeShiftIntensityMero a (a + (n : ℂ))))
      (gammaOppositeShiftWignerSmithLogMero a (a + (n : ℂ))) := by
  exact HTGeometry.no_scalarAwareFiniteDifferentialCircuit_wignerSmith_from_daObservation
    (gammaOppositeShiftQuotientMero a (a + (n : ℂ)))
    (gammaOppositeShiftIntensityMero a (a + (n : ℂ)))
    (hypertranscendentalOver_gammaOppositeShiftQuotientMero a (a + (n : ℂ)))
    (differentialAlgebraicOver_gammaOppositeShiftIntensityMero_add_nat a n)

end

end GaloisForLFunctions
