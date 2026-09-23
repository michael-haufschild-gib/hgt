import GaloisForLFunctions.HTGeometry.ExponentialMemoryTransportCurvature
import GaloisForLFunctions.RHTower.DQPTProbeDensityMatrix
import GaloisForLFunctions.RHTower.RiemannSourceForcedHorizontalVanishingFrontier
import Mathlib.Tactic

/-!
# DQPT tomography of the Riemann-source memory lag

The exponential-memory response from arXiv:2608.09607 becomes a concrete noncommutative probe
when its two modes are the Pauli `X` and `Z` generators of the DQPT probe qubit.  Pauli-`Y`
tomography reads their commutator coefficient without loss: the reporter value is exactly
`-4i x/(1+x²)`.

Feeding the canonical source-horizontal Gamma/co-Poisson parameter into that probe produces a
bounded signed physical landing shared by the source entropy, unsquared Gaussian Wronskian,
Gamma/co-Poisson boundary defect, and centered Xi charge.  Its zero locus is exactly the critical
line.  Global annihilation is therefore equivalent to the existing source-forced horizontal
frontier and to RH; this module constructs the coefficient-faithful landing but does not assert
that annihilation.
-/

open Complex Matrix
open scoped Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open DQPT

/-- Pauli-`Y` tomography of a two-by-two DQPT probe observable. -/
def dqptSigmaYLagReporter :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 2) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ dqptSigmaY)

@[simp]
theorem dqptSigmaYLagReporter_apply (M : Matrix (Fin 2) (Fin 2) ℂ) :
    dqptSigmaYLagReporter M = (dqptSigmaY * M).trace := by
  rfl

/-- The DQPT reporter is coefficient-faithful on the Pauli `X/Z` commutator. -/
theorem dqptSigmaYLagReporter_commutator_XZ :
    dqptSigmaYLagReporter (matrixCommutator dqptSigmaX dqptSigmaZ) =
      -4 * Complex.I := by
  simp [dqptSigmaYLagReporter, dqptSigmaX, dqptSigmaY, dqptSigmaZ,
    matrixCommutator, Matrix.trace, Fin.sum_univ_two]
  ring

theorem dqptSigmaYLagReporter_commutator_XZ_ne_zero :
    dqptSigmaYLagReporter (matrixCommutator dqptSigmaX dqptSigmaZ) ≠ 0 := by
  rw [dqptSigmaYLagReporter_commutator_XZ]
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

/-- Canonical Riemann-source horizontal grade inserted as the DQPT present/memory lag. -/
def riemannSourceDQPTMemoryLagCurvature
    (rho : XiDivisorSupport) : Matrix (Fin 2) (Fin 2) ℂ :=
  exponentialMemoryLagCurvature dqptSigmaX dqptSigmaZ
    (riemannSourceGammaCoPoissonHorizontalParameter rho) 1 0

/-- Exact tomographic response of the Riemann-source DQPT lag. -/
theorem dqptSigmaYLagReporter_riemannSourceDQPTMemoryLagCurvature_eq
    (rho : XiDivisorSupport) :
    dqptSigmaYLagReporter (riemannSourceDQPTMemoryLagCurvature rho) =
      ((riemannSourceGammaCoPoissonHorizontalParameter rho : ℂ) /
        (1 + (riemannSourceGammaCoPoissonHorizontalParameter rho : ℂ) ^ (2 : ℕ))) *
          (-4 * Complex.I) := by
  rw [riemannSourceDQPTMemoryLagCurvature,
    exponentialMemoryLagCurvature_axis_eq, LinearMap.map_smul,
    dqptSigmaYLagReporter_commutator_XZ]
  rfl

/-- The DQPT lag reporter loses no horizontal information on any Xi divisor fibre. -/
theorem dqptSigmaYLagReporter_riemannSourceDQPTMemoryLagCurvature_eq_zero_iff
    (rho : XiDivisorSupport) :
    dqptSigmaYLagReporter (riemannSourceDQPTMemoryLagCurvature rho) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [riemannSourceDQPTMemoryLagCurvature,
    exponentialMemoryLagCurvature_axis_reporter_eq_zero_iff
      dqptSigmaX dqptSigmaZ dqptSigmaYLagReporter
        dqptSigmaYLagReporter_commutator_XZ_ne_zero,
    riemannSourceGammaCoPoissonHorizontalParameter_eq_greenFracture_re,
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [ofReal_re]
  constructor <;> intro h <;> linarith

/-- Global physical annihilation statement for the coefficient-faithful DQPT lag landing. -/
def DQPTMemoryLagHorizontalVanishes : Prop :=
  ∀ rho : XiDivisorSupport,
    dqptSigmaYLagReporter (riemannSourceDQPTMemoryLagCurvature rho) = 0

/-- DQPT lag annihilation is exactly the common source-forced horizontal frontier. -/
theorem dqptMemoryLagHorizontalVanishes_iff_sourceForcedHorizontalVanishing :
    DQPTMemoryLagHorizontalVanishes ↔ XiSourceForcedHorizontalVanishing := by
  apply forall_congr'
  intro rho
  rw [dqptSigmaYLagReporter_riemannSourceDQPTMemoryLagCurvature_eq_zero_iff,
    riemannSourceGammaCoPoissonHorizontalDefect_eq_zero_iff]

/-- Exact endpoint audit: the new physical landing exposes, but does not assume, the RH-strength
annihilation obligation. -/
theorem dqptMemoryLagHorizontalVanishes_iff_riemannHypothesis :
    DQPTMemoryLagHorizontalVanishes ↔ RiemannHypothesis := by
  rw [dqptMemoryLagHorizontalVanishes_iff_sourceForcedHorizontalVanishing,
    xiSourceForcedHorizontalVanishing_iff_riemannHypothesis]

end

end RHTower
