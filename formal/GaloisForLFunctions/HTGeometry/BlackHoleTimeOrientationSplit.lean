import GaloisForLFunctions.HTGeometry.BlackHoleDressedLogSpectralClock
import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability
import GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary

/-!
# Time-orientation split of the Schwarzschild far-zone dressed logarithm

Solon's all-order Schwarzschild response contains the retarded dressed logarithm

`tau_ret(eta) = L + 2 * (digamma(1 - eta) + gamma_E)`.

Its time-reflected partner replaces `eta` by `-eta`.  This module proves an exact and sharp split:

* the antisymmetric combination is differentially algebraic, because it is `-2` times the
  logarithmic derivative of `Gamma(1 + eta) * Gamma(1 - eta)`;
* the symmetric combination is hypertranscendental, because it is a DA constant plus `2` times
  the Wigner--Smith clock of `Gamma(1 + eta) / Gamma(1 - eta)`;
* rational clocks and the antisymmetric channel cannot reconstruct the symmetric channel through
  any finite differential circuit.

The result classifies the universal far-zone coordinate, not the full nonlinear Love response.
The Gamma/zeta tower comes from the far-zone Newtonian phase; no horizon-microstate or quantum
witness claim is made.

Physics provenance: M. P. Solon, *Universal Closed Form for Dynamical Love Numbers of Black Holes*,
arXiv:2606.19281 (2026).
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The DA constant `L + 2 gamma_E` common to the two time orientations. -/
def blackHoleDressedLogConstantMero (scaleLog : ℂ) : meroField Set.univ :=
  algebraMap (RatFunc ℂ) (meroField Set.univ)
    (RatFunc.C (scaleLog + 2 * (Real.eulerMascheroniConstant : ℂ)))

/-- Retarded Schwarzschild far-zone dressed log as a global meromorphic element.  Since
`gammaNegativeLogDerivativeMero 1 = -digamma(1-eta)`, this is the meromorphic representative of
`L + 2 * (digamma(1-eta) + gamma_E)`. -/
def blackHoleFarZoneRetardedDressedLogMero
    (scaleLog : ℂ) : meroField Set.univ :=
  blackHoleDressedLogConstantMero scaleLog -
    2 * gammaNegativeLogDerivativeMero 1

/-- Time-reflected/advanced Schwarzschild far-zone dressed log. -/
def blackHoleFarZoneAdvancedDressedLogMero
    (scaleLog : ℂ) : meroField Set.univ :=
  blackHoleDressedLogConstantMero scaleLog +
    2 * digammaShiftMero 1

/-- Sum of the retarded and advanced dressed logs. -/
def blackHoleFarZoneTimeSymmetricDressedLogMero
    (scaleLog : ℂ) : meroField Set.univ :=
  blackHoleFarZoneRetardedDressedLogMero scaleLog +
    blackHoleFarZoneAdvancedDressedLogMero scaleLog

/-- Difference of the retarded and advanced dressed logs. -/
def blackHoleFarZoneTimeAntisymmetricDressedLogMero
    (scaleLog : ℂ) : meroField Set.univ :=
  blackHoleFarZoneRetardedDressedLogMero scaleLog -
    blackHoleFarZoneAdvancedDressedLogMero scaleLog

/-- **Time-symmetric value relation.**  The symmetric dressed log is a DA constant plus twice the
HT Wigner--Smith clock of the opposite-orientation Gamma quotient. -/
theorem blackHoleFarZoneTimeSymmetricDressedLogMero_eq_wignerSmith
    (scaleLog : ℂ) :
    blackHoleFarZoneTimeSymmetricDressedLogMero scaleLog =
      2 * blackHoleDressedLogConstantMero scaleLog +
        2 * gammaOppositeShiftWignerSmithLogMero 1 1 := by
  rw [blackHoleFarZoneTimeSymmetricDressedLogMero,
    blackHoleFarZoneRetardedDressedLogMero,
    blackHoleFarZoneAdvancedDressedLogMero,
    gammaOppositeShiftWignerSmithLogMero_eq_orientedLogDerivatives]
  ring

/-- **Time-antisymmetric value relation.**  The orientation difference is `-2` times the
logarithmic derivative of the integral-shift Gamma product. -/
theorem blackHoleFarZoneTimeAntisymmetricDressedLogMero_eq_productLogDeriv
    (scaleLog : ℂ) :
    blackHoleFarZoneTimeAntisymmetricDressedLogMero scaleLog =
      -2 * Differential.logDeriv (gammaOppositeShiftProductMero 1 1) := by
  have hpositive : gammaShiftMero (1 : ℂ) ≠ 0 :=
    gammaShiftMero_ne_zero 1
  have hnegative : gammaNegativeShiftMero (1 : ℂ) ≠ 0 := by
    rw [gammaNegativeShiftMero_reflection]
    exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero 1)
      (inv_ne_zero (gammaShiftMero_ne_zero (1 - 1)))
  rw [blackHoleFarZoneTimeAntisymmetricDressedLogMero,
    blackHoleFarZoneRetardedDressedLogMero,
    blackHoleFarZoneAdvancedDressedLogMero,
    gammaOppositeShiftProductMero, Differential.logDeriv_mul _ _
      hpositive hnegative]
  unfold digammaShiftMero gammaNegativeLogDerivativeMero
  ring

/-- **The time-antisymmetric dressed-log source is DA.**  The two Gamma shifts sum to the integer
`2`, so Euler reflection collapses their product to a DA sine--rational gauge. -/
theorem differentialAlgebraicOver_blackHoleFarZoneTimeAntisymmetricDressedLogMero
    (scaleLog : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (blackHoleFarZoneTimeAntisymmetricDressedLogMero scaleLog) := by
  have hproduct :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaOppositeShiftProductMero (1 : ℂ) 1) := by
    have hreflect :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (gammaReflectionProductMero (1 : ℂ)) :=
      (differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight
        1).2 ⟨-1, by norm_num⟩
    simpa [gammaReflectionProductMero, gammaOppositeShiftProductMero] using
      hreflect
  have hlog :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (Differential.logDeriv (gammaOppositeShiftProductMero (1 : ℂ) 1)) := by
    simpa only [Differential.logDeriv] using
      (differentialAlgebraicOver_deriv_div_self hproduct)
  have hscaled :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (-2 * Differential.logDeriv
          (gammaOppositeShiftProductMero (1 : ℂ) 1)) := by
    have hsum := HTGeometry.differentialAlgebraicOver_add hlog hlog
    have hneg := HTGeometry.differentialAlgebraicOver_neg hsum
    convert hneg using 1
    ring
  exact
    (blackHoleFarZoneTimeAntisymmetricDressedLogMero_eq_productLogDeriv
      scaleLog).symm ▸ hscaled

/-- **The time-symmetric dressed-log source is HT.**  Time reflection does not cancel the
opposite-orientation Gamma quotient or its Wigner--Smith clock. -/
theorem hypertranscendentalOver_blackHoleFarZoneTimeSymmetricDressedLogMero
    (scaleLog : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (blackHoleFarZoneTimeSymmetricDressedLogMero scaleLog) := by
  rw [blackHoleFarZoneTimeSymmetricDressedLogMero_eq_wignerSmith]
  have hclock :
      HypertranscendentalOver (RatFunc ℂ)
        (gammaOppositeShiftWignerSmithLogMero (1 : ℂ) 1) :=
    hypertranscendentalOver_gammaOppositeShiftWignerSmithLogMero 1 1
  have htwoDA :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (2 : meroField Set.univ) := by
    have hone :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (1 : meroField Set.univ) := by
      simpa only [map_one] using
        (HTGeometry.differentialAlgebraicOver_algebraMap
          (1 : RatFunc ℂ) :
          DifferentialAlgebraicOver (RatFunc ℂ)
            (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))
    simpa only [one_add_one_eq_two] using
      (HTGeometry.differentialAlgebraicOver_add hone hone)
  have hscaled :
      HypertranscendentalOver (RatFunc ℂ)
        (2 * gammaOppositeShiftWignerSmithLogMero (1 : ℂ) 1) := by
    simpa [mul_comm] using
      (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
        htwoDA (by norm_num : (2 : meroField Set.univ) ≠ 0)).2 hclock
  have hconstant :
      DifferentialAlgebraicOver (RatFunc ℂ)
        (2 * blackHoleDressedLogConstantMero scaleLog) := by
    apply HTGeometry.differentialAlgebraicOver_mul htwoDA
    exact HTGeometry.differentialAlgebraicOver_algebraMap
      (RatFunc.C
        (scaleLog + 2 * (Real.eulerMascheroniConstant : ℂ)))
  simpa [add_comm] using
    (HTGeometry.hypertranscendentalOver_add_differentialAlgebraic_iff
      hconstant).2 hscaled

/-- **Finite-recovery obstruction.**  Rational clocks and the DA orientation difference cannot
finitely reconstruct the common HT memory retained by the symmetric channel. -/
theorem no_scalarAwareFiniteDifferentialCircuit_blackHoleTimeSymmetric_from_antisymmetric
    (scaleLog : ℂ) :
    ¬ HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ)
        (fun a =>
          a = blackHoleFarZoneTimeAntisymmetricDressedLogMero scaleLog))
      (blackHoleFarZoneTimeSymmetricDressedLogMero scaleLog) := by
  intro hcircuit
  obtain ⟨a, ha, hHT⟩ :=
    HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
      (hypertranscendentalOver_blackHoleFarZoneTimeSymmetricDressedLogMero
        scaleLog) hcircuit
  rw [ha] at hHT
  exact hHT
    (differentialAlgebraicOver_blackHoleFarZoneTimeAntisymmetricDressedLogMero
      scaleLog)

end

end GaloisForLFunctions
