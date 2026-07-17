import GaloisForLFunctions.HTGeometry.WignerSmithLogClockObservability

/-!
# Wigner--Smith observability of the thermal CFT Gamma response

The thermal CFT frequency response of `ThermalCFTGammaResponseBoundary` is a reflected Gamma
kernel multiplied by an elementary exponential readout.  Its logarithmic frequency current is a
standard scalar Wigner--Smith observable.  Restoring the exponential phase shifts that current by
exactly its constant calibration `lambda`; it does not change the differential boundary.

Consequently the Wigner--Smith current is differentially algebraic exactly on the same
half-integral conformal-weight lattice as the response itself, and is hypertranscendental at every
other weight.  The result concerns what a frequency observer can read from the thermal/holographic
clock, not evolution of the CFT state.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance thermalCFTWignerSmithDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance thermalCFTWignerSmithComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance thermalCFTWignerSmithComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance thermalCFTWignerSmithDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance thermalCFTWignerSmithRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance thermalCFTWignerSmithRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance thermalCFTWignerSmithDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance thermalCFTWignerSmithCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

theorem gammaReflectionProductMero_ne_zero (h : ℂ) :
    gammaReflectionProductMero h ≠ 0 := by
  exact mul_ne_zero (gammaShiftMero_ne_zero h)
    (by
      rw [gammaNegativeShiftMero_reflection]
      exact mul_ne_zero (gammaReflectionGaugeMero_ne_zero h)
        (inv_ne_zero (gammaShiftMero_ne_zero (1 - h))))

/-- Wigner--Smith/logarithmic current of the reflected Gamma core. -/
def thermalCFTGammaWignerSmithLogClockMero (h : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock (gammaReflectionProductMero h)

/-- Wigner--Smith/logarithmic current of the complete exponential-dressed response. -/
def thermalCFTResponseWignerSmithLogClockMero
    (h lambda : ℂ) : meroField Set.univ :=
  HTGeometry.wignerSmithLogClock (thermalCFTFrequencyResponseMero h lambda)

/-- **Thermal-CFT delay gauge law.**  The elementary phase calibration adds exactly `lambda` to
the logarithmic response current. -/
theorem thermalCFTResponseWignerSmithLogClockMero_eq_gamma_add_const
    (h lambda : ℂ) :
    thermalCFTResponseWignerSmithLogClockMero h lambda =
      thermalCFTGammaWignerSmithLogClockMero h +
        algebraMap ℂ (meroField Set.univ) lambda := by
  unfold thermalCFTResponseWignerSmithLogClockMero
    thermalCFTGammaWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
    thermalCFTFrequencyResponseMero
  rw [Differential.logDeriv_mul]
  · congr 1
    unfold Differential.logDeriv
    rw [physicalExponentialMero_deriv]
    field_simp [physicalExponentialMero_ne_zero lambda]
  · exact gammaReflectionProductMero_ne_zero h
  · exact physicalExponentialMero_ne_zero lambda

/-- **Exact thermal/holographic delay boundary.**  The logarithmic response current is DA exactly
on the integral `1-2*h` weight lattice. -/
theorem differentialAlgebraicOver_thermalCFTResponseWignerSmithLogClockMero_iff_integerWeight
    (h lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (thermalCFTResponseWignerSmithLogClockMero h lambda) ↔
      ∃ k : ℤ, 1 - 2 * h = (k : ℂ) := by
  constructor
  · intro hdelay
    by_contra hweight
    have hHT : HypertranscendentalOver (RatFunc ℂ)
        (thermalCFTResponseWignerSmithLogClockMero h lambda) := by
      rw [thermalCFTResponseWignerSmithLogClockMero,
        HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff,
        hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight]
      simpa only [not_exists] using hweight
    exact hHT hdelay
  · intro hweight
    unfold thermalCFTResponseWignerSmithLogClockMero HTGeometry.wignerSmithLogClock
    unfold Differential.logDeriv
    exact differentialAlgebraicOver_deriv_div_self
      ((differentialAlgebraicOver_thermalCFTFrequencyResponseMero_iff_integerWeight
        h lambda).2 hweight)

/-- Generic conformal weight remains HT after passing from the thermal response to its directly
observable logarithmic delay. -/
theorem hypertranscendentalOver_thermalCFTResponseWignerSmithLogClockMero_iff_nonintegerWeight
    (h lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (thermalCFTResponseWignerSmithLogClockMero h lambda) ↔
      ∀ k : ℤ, 1 - 2 * h ≠ (k : ℂ) := by
  rw [thermalCFTResponseWignerSmithLogClockMero,
    HTGeometry.hypertranscendentalOver_wignerSmithLogClock_iff,
    hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight]

end

end GaloisForLFunctions
