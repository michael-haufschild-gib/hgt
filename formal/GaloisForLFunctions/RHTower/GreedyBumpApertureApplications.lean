import GaloisForLFunctions.HTGeometry.GreedyBumpLocalGeometry
import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric
import GaloisForLFunctions.RHTower.XiTransverseValuationGaussianRadicalConnector

/-!
# Greedy-bump laws for aperture and valuation Gram metrics

This file transports the paper's complete local-search package to strict
finite Gram metrics already built from Möbius aperture and valuation packets.
-/

open Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Distinct nonzero continuous apertures at one prime. -/
structure GreedyBumpContinuousApertureData (N : ℕ) where
  aperture : Fin N → ℝ
  prime : Nat.Primes
  injective : Function.Injective aperture
  nonzero : ∀ j, aperture j ≠ 0

/-- Finite continuous-aperture source Gram as template metric. -/
def GreedyBumpContinuousApertureData.metric {N : ℕ}
    (A : GreedyBumpContinuousApertureData N) : PositiveTemplateMetric N where
  matrix := xiMobiusPrimeContinuousApertureFiniteGramMatrix A.aperture A.prime
  posDef := (xiMobiusPrimeContinuousApertureFiniteGramMatrix_posDef_iff_injective_ne_zero
    A.aperture A.prime).mpr ⟨A.injective, A.nonzero⟩

/-- All fourteen local-search laws hold on finite continuous-aperture packets. -/
theorem greedyBump_continuousAperture_laws {N : ℕ}
    (A : GreedyBumpContinuousApertureData N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q A.metric :=
  greedyBumpMetricLaws_closed Q A.metric

/-- Distinct positive continuous apertures for the completed Szegő metric. -/
structure GreedyBumpSzegoApertureData (N : ℕ) where
  aperture : Fin N → ℝ
  prime : Nat.Primes
  injective : Function.Injective aperture
  positive : ∀ j, 0 < aperture j

/-- Completed continuous-aperture Szegő Gram as template metric. -/
def GreedyBumpSzegoApertureData.metric {N : ℕ}
    (A : GreedyBumpSzegoApertureData N) : PositiveTemplateMetric N where
  matrix := xiMobiusPrimeContinuousApertureSzegoGramMatrix A.aperture A.prime
  posDef := (xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_injective_pos
    A.aperture A.prime).mpr ⟨A.injective, A.positive⟩

/-- All fourteen local-search laws hold on completed Szegő aperture packets. -/
theorem greedyBump_szegoAperture_laws {N : ℕ}
    (A : GreedyBumpSzegoApertureData N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q A.metric :=
  greedyBumpMetricLaws_closed Q A.metric

/-- Distinct integral shifts with positive Gaussian bandwidth. -/
structure GreedyBumpValuationGaussianData (N : ℕ) where
  shift : Fin N → ℕ
  prime : Nat.Primes
  bandwidth : PositiveSignal
  injective : Function.Injective shift

/-- First-valuation Gaussian distance Gram as template metric. -/
def GreedyBumpValuationGaussianData.metric {N : ℕ}
    (A : GreedyBumpValuationGaussianData N) : PositiveTemplateMetric N where
  matrix := xiTransversePrimeFirstValuationGaussianGramMatrixAt
    A.shift A.prime A.bandwidth
  posDef := (xiTransversePrimeFirstValuationGaussianGramMatrixAt_posDef_iff_injective
    A.shift A.prime A.bandwidth.property).mpr A.injective

/-- All fourteen local-search laws hold for first-valuation Gaussian packets. -/
theorem greedyBump_valuationGaussian_laws {N : ℕ}
    (A : GreedyBumpValuationGaussianData N) (Q : PositiveSignal) :
    GreedyBumpMetricLaws Q A.metric :=
  greedyBumpMetricLaws_closed Q A.metric

/-- Prime and Gaussian bandwidth change volume, but not matched bias. -/
theorem greedyBump_valuationGaussian_bias_prime_bandwidth_invariant
    {N : ℕ} (A B : GreedyBumpValuationGaussianData N) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q A.metric)⁻¹ * A.metric.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q B.metric)⁻¹ * B.metric.matrix) := by
  rw [(greedyBump_valuationGaussian_laws A Q).localBias,
    (greedyBump_valuationGaussian_laws B Q).localBias]

/-- Radically different aperture metrics retain the same dimension-only local bias. -/
theorem greedyBump_apertureMetric_bias_radicalInvariant
    {N : ℕ} (A : GreedyBumpContinuousApertureData N)
    (B : GreedyBumpSzegoApertureData N) (Q : PositiveSignal) :
    (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q A.metric)⁻¹ * A.metric.matrix) =
      (1 / 2 : ℝ) * Matrix.trace
        ((greedyBumpHessian Q B.metric)⁻¹ * B.metric.matrix) := by
  rw [(greedyBump_continuousAperture_laws A Q).localBias,
    (greedyBump_szegoAperture_laws B Q).localBias]

end

end GaloisForLFunctions.RHTower
